//! `imports SRC_DIR…` builds the import graph of the Rust files of each crate source directory
//! and reports its cycles (step S.1f). Zed forbids a cycle between files (sec:units), so the
//! Rust-hosted compiler, which is ported file by file, must have none either.
//!
//! The files are those the crate roots `lib.rs`, `main.rs` and `bin/*.rs` reach by `mod`
//! declarations. A `mod` declaration is no edge: a directory is a namespace in Zed, not a unit.
//! A file imports another when a `use` declaration or a path in its code (`crate::a::B`,
//! `super::b::f`, or a path through a name a `use` binds) names an item the other file defines.
//! A re-export is resolved to the file that defines the item, and the `use` that re-exports it is
//! itself an import of that file. A path that names only a module (`use crate::store;`) is no
//! edge until a path through it names an item. A glob import (`use super::*;`) is an edge to the
//! file of the module or enum it names, and a name it brings in is looked up through it. A name
//! a module neither declares nor brings in (one a macro makes) is taken to be the module's own,
//! so the edge goes to the module's file, whose own imports then lead on to the defining file:
//! the graph may hold a path through an extra file then, but never misses a cycle. Paths into
//! other crates (`std::`, `zed_kernel::`) are no edges, so the edges of a binary root into its
//! library are not drawn; a library cannot import its binary, so they close no cycle.
//!
//! A call of a method written in an `impl` block in another file than its type's
//! (`impl Builder { … }` split over several files) is an import of the block's file: a Zed port
//! makes that block a unit of its own, which the caller imports. The receiver's type is found
//! from the parameters, `let`s, fields, return types and paths the call chain starts from, with
//! the standard wrappers (`Box`, `Rc`, `&`, `Option`, `Vec`, …) seen through. When it is not
//! found, the call is an import of every file with a method of that name written apart from its
//! type, so no cycle is missed; the report counts those calls. A call of a method written in
//! its type's own file needs no edge: the caller already imports that file by naming the type
//! (or reaches it through the file that gave it the value), so such an edge closes no cycle the
//! graph does not already have. Trait methods are written with their trait or their type, which
//! the caller names, so they too need none.
//!
//! A cycle is a strongly connected component of two files or more (a file naming its own items
//! is no edge). Each is reported with its files, a shortest cycle through its first file, and
//! every import within it, each cited by file and line. The scan is one pass over the text, the
//! resolution one hash lookup per segment of a path, the typing of the calls one pass over each
//! file with a hash lookup per token, and the components are found by Tarjan's algorithm with
//! an explicit stack in O(n + e), n the bytes of the files and e the imports between them.
//! Sorting each file's imports, for the report and the citations, makes the whole
//! O(n + e log e) (COMPLEXITY F103).

mod lex;

use lex::{Tok, lex, mates};

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{Outcome, arg, say};

const USAGE: &str = "imports SRC_DIR…";

/// Builds and checks the import graph of each directory of `args`; passes when none has a cycle.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    arg(args, 0, USAGE)?;
    let mut acyclic = true;
    for dir in args {
        let files = read_sources(dir)?;
        let graph = Graph::of(&files)?;
        let cycles = graph.cycles();
        report(dir, &graph, &cycles, out);
        acyclic &= cycles.is_empty();
    }
    Ok(acyclic)
}

/// Every `.rs` file under `dir`, as its path relative to `dir` with `/` separators and its text,
/// sorted by path.
pub fn read_sources(dir: &str) -> Result<Vec<(String, String)>, String> {
    let mut files = Vec::new();
    let mut todo = vec![String::new()];
    while let Some(rel) = todo.pop() {
        let at = if rel.is_empty() {
            dir.to_string()
        } else {
            format!("{dir}/{rel}")
        };
        let entries = std::fs::read_dir(&at).map_err(|e| format!("{at}: {e}"))?;
        for entry in entries {
            let entry = entry.map_err(|e| format!("{at}: {e}"))?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or_else(|| format!("{at}: a file name that is not UTF-8"))?;
            let path = if rel.is_empty() {
                name.to_string()
            } else {
                format!("{rel}/{name}")
            };
            let kind = entry.file_type().map_err(|e| format!("{at}/{name}: {e}"))?;
            if kind.is_dir() {
                todo.push(path);
            } else if name.ends_with(".rs") {
                let text = crate::text::read_text(&format!("{dir}/{path}"))?;
                files.push((path, text));
            }
        }
    }
    files.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    Ok(files)
}

/// Where an import is written: the line and the path as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cite {
    /// The line of the path's last segment, from 1.
    pub line: usize,
    /// The path, its segments joined by `::`.
    pub path: String,
}

/// The import graph: the files the crate roots reach and the imports between them.
#[derive(Debug)]
pub struct Graph {
    /// The files read, in the order they were given (`read_sources` gives them sorted by path).
    pub files: Vec<String>,
    /// For each file, the files it imports, sorted, each with the first place it does so.
    pub imports: Vec<Vec<(usize, Cite)>>,
    /// The `.rs` files no `mod` declaration reaches, left out of the graph.
    pub undeclared: usize,
    /// The `mod name;` declarations a `#[path]` attribute places, which are not read, each as
    /// `file:line`.
    pub placed: Vec<String>,
    /// The calls of a method written apart from its type whose receiver's type was not found,
    /// each an import of every file with a method of that name written apart from its type.
    pub unknown_calls: usize,
    /// The inherent `impl` blocks whose type was not found in the crate.
    pub loose_impls: usize,
}

impl Graph {
    /// The graph of `files`, each a path relative to the crate source directory and its text.
    pub fn of(files: &[(String, String)]) -> Result<Graph, String> {
        Builder::new(files)?.finish()
    }

    /// The strongly connected components of two files or more, each sorted, in the order of
    /// their first files.
    pub fn cycles(&self) -> Vec<Vec<usize>> {
        let mut found = tarjan(&self.imports);
        found.retain(|c| c.len() > 1);
        for c in &mut found {
            c.sort_unstable();
        }
        found.sort_unstable();
        found
    }

    /// A shortest cycle through the first file of `component`, within it: the files in order,
    /// the first not repeated at the end.
    pub fn shortest_cycle(&self, component: &[usize]) -> Vec<usize> {
        let inside: HashSet<usize> = component.iter().copied().collect();
        let start = component[0];
        let mut before: HashMap<usize, usize> = HashMap::new();
        let mut queue = VecDeque::from([start]);
        while let Some(f) = queue.pop_front() {
            for &(g, _) in &self.imports[f] {
                if g == start {
                    // The way back from `f` through the files that found each other ends at
                    // `start`, which nothing found.
                    let mut cycle = vec![f];
                    let mut at = f;
                    while let Some(&p) = before.get(&at) {
                        cycle.push(p);
                        at = p;
                    }
                    cycle.reverse();
                    return cycle;
                }
                if inside.contains(&g) && g != start && !before.contains_key(&g) {
                    before.insert(g, f);
                    queue.push_back(g);
                }
            }
        }
        // Every file of a strongly connected component of two or more reaches its first file.
        vec![start]
    }
}

/// Writes the report on the graph of `dir` and its `cycles`.
fn report(dir: &str, graph: &Graph, cycles: &[Vec<usize>], out: &mut String) {
    let edges: usize = graph.imports.iter().map(Vec::len).sum();
    say!(
        out,
        "{dir}: {} files, {edges} imports between files",
        graph.files.len()
    );
    if graph.undeclared > 0 {
        say!(
            out,
            "{} .rs files no mod declaration reaches, left out",
            graph.undeclared
        );
    }
    if !graph.placed.is_empty() {
        say!(
            out,
            "modules a #[path] attribute places, not read: {}",
            graph.placed.join(", ")
        );
    }
    if graph.unknown_calls > 0 {
        say!(
            out,
            "{} calls of a method written apart from its type, receiver not typed",
            graph.unknown_calls
        );
    }
    if graph.loose_impls > 0 {
        say!(
            out,
            "{} impl blocks whose type is not found",
            graph.loose_impls
        );
    }
    if cycles.is_empty() {
        say!(out, "no import cycle");
        return;
    }
    let name = |f: usize| graph.files[f].as_str();
    for (i, component) in cycles.iter().enumerate() {
        let files: Vec<&str> = component.iter().map(|&f| name(f)).collect();
        say!(
            out,
            "cycle {} of {}: {} files: {}",
            i + 1,
            cycles.len(),
            files.len(),
            files.join(", ")
        );
        let cycle = graph.shortest_cycle(component);
        say!(out, "  a shortest cycle through {}:", name(cycle[0]));
        for (k, &f) in cycle.iter().enumerate() {
            let g = cycle[(k + 1) % cycle.len()];
            if let Some(cite) = cite_of(graph, f, g) {
                say!(
                    out,
                    "    {}:{} {} -> {}",
                    name(f),
                    cite.line,
                    cite.path,
                    name(g)
                );
            }
        }
        say!(out, "  every import within it:");
        let inside: HashSet<usize> = component.iter().copied().collect();
        for &f in component {
            for (g, cite) in &graph.imports[f] {
                if inside.contains(g) {
                    say!(
                        out,
                        "    {}:{} {} -> {}",
                        name(f),
                        cite.line,
                        cite.path,
                        name(*g)
                    );
                }
            }
        }
    }
}

/// The place `f` imports `g`, by binary search in `f`'s sorted imports.
fn cite_of(graph: &Graph, f: usize, g: usize) -> Option<&Cite> {
    let imports = &graph.imports[f];
    imports
        .binary_search_by_key(&g, |&(h, _)| h)
        .ok()
        .map(|i| &imports[i].1)
}

/// The strongly connected components of the graph `next`, by Tarjan's algorithm with an
/// explicit stack, so a long chain of files cannot overflow the call stack. O(n + e).
fn tarjan<T>(next: &[Vec<(usize, T)>]) -> Vec<Vec<usize>> {
    const UNSEEN: usize = usize::MAX;
    let n = next.len();
    let (mut index, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut on_stack = vec![false; n];
    let (mut stack, mut found) = (Vec::new(), Vec::new());
    let mut count = 0;
    // Each frame is a file and the position of the next import of it to follow.
    let mut frames: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if index[root] != UNSEEN {
            continue;
        }
        frames.push((root, 0));
        while let Some(frame) = frames.last_mut() {
            let (v, i) = *frame;
            if i == 0 {
                index[v] = count;
                low[v] = count;
                count += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if let Some(&(w, _)) = next[v].get(i) {
                frame.1 = i + 1;
                if index[w] == UNSEEN {
                    frames.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            // `v` is finished: its frame goes, and its low link passes to the file that
            // followed an import to it.
            frames.pop();
            if let Some(&(u, _)) = frames.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                found.push(component);
            }
        }
    }
    found
}

/// The keywords that begin an item whose name follows them.
const ITEMS: &[&str] = &[
    "fn", "struct", "enum", "union", "trait", "type", "const", "static",
];

/// The standard wrappers a method call or a field access sees through to the value inside.
const THROUGH: &[&str] = &[
    "Box",
    "Rc",
    "Arc",
    "Cow",
    "RefCell",
    "Ref",
    "RefMut",
    "Cell",
    "Mutex",
    "MutexGuard",
    "RwLock",
    "ManuallyDrop",
    "Pin",
];

/// The words that are never a name a pattern binds.
const KEYWORDS: &[&str] = &[
    "as", "async", "await", "box", "break", "const", "continue", "crate", "dyn", "else", "enum",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
    "ref", "return", "self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use",
    "where", "while",
];

/// A module: a file, or a `mod name { … }` written inside one.
struct Module<'a> {
    file: usize,
    parent: Option<usize>,
    root: usize,
    /// The directory its `mod name;` declarations are read from.
    dir: String,
    children: HashMap<&'a str, usize>,
    items: HashSet<&'a str>,
    /// The names its `use` declarations bind, each to its binding.
    bound: HashMap<&'a str, usize>,
    /// Its glob imports (`use super::*;`), as bindings.
    globs: Vec<usize>,
    /// Its child modules a `#[path]` attribute places, which are not read: a path through one
    /// leads outside the graph.
    placed: HashSet<&'a str>,
}

/// A `use` declaration's leaf: the path it names, in the module it is written in.
struct Binding<'a> {
    module: usize,
    segs: Vec<&'a str>,
    glob: bool,
    line: usize,
}

/// A path written in code, in the module it is written in.
struct Path<'a> {
    module: usize,
    segs: Vec<&'a str>,
    line: usize,
}

/// What a path resolves to.
#[derive(Clone, Copy, Debug)]
enum Res<'a> {
    Module(usize),
    /// An item of the module, by name.
    Item(usize, &'a str),
    /// Something outside the crate, or a local name.
    Outside,
}

/// The progress of resolving a path.
enum Step<'a> {
    Done(Res<'a>),
    /// The path goes through a binding not yet resolved.
    Need(usize),
}

/// What an open brace opens.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Opening {
    Module(usize),
    Impl(usize),
    Fn(usize),
    Other,
}

/// A function with a body: a free function, a method, or one inside another's body.
struct FnRec<'a> {
    file: usize,
    module: usize,
    name: &'a str,
    /// The `impl` block it is written in, directly.
    imp: Option<usize>,
    /// The positions of the parentheses of its parameters.
    params: (usize, usize),
    /// Whether its first parameter is `self`, so `x.name(…)` can call it.
    method: bool,
    /// The tokens of its return type.
    ret: Option<(usize, usize)>,
    /// The path, from `module`, of the module its visibility opens it to: empty for a private
    /// function, `super` for `pub(super)`, `crate` for `pub` and `pub(crate)`.
    vis: Vec<&'a str>,
}

/// An `impl` block.
struct ImplRec {
    file: usize,
    module: usize,
    /// The tokens of the type it is for.
    ty: (usize, usize),
    /// An `impl Type`, not an `impl Trait for Type`.
    inherent: bool,
    /// An `impl Deref for Type`.
    deref: bool,
    /// The tokens of its `type Target = …;`.
    target: Option<(usize, usize)>,
    methods: Vec<usize>,
    /// The definition of its type, once found.
    def: Option<usize>,
}

/// A field's name: `name` or a position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Field<'a> {
    Named(&'a str),
    Pos(usize),
}

/// A struct, enum, union or type alias of a module.
struct Def<'a> {
    file: usize,
    module: usize,
    name: &'a str,
    /// Each field and the tokens of its type.
    fields: Fields<'a>,
    /// The tokens of the type an alias names.
    alias: Option<(usize, usize)>,
    /// The fields of each variant of an enum.
    variants: HashMap<&'a str, Fields<'a>>,
    /// The methods of its inherent `impl` blocks, by name.
    methods: HashMap<&'a str, Vec<usize>>,
    /// The type its `Deref` gives.
    deref: Option<Text>,
}

/// A type written in the source: its tokens, the module its names are read in, and what `Self`
/// means there.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Text {
    file: usize,
    span: (usize, usize),
    module: usize,
    self_def: Option<usize>,
}

/// The type of a value, as far as finding the file of a method it calls needs.
#[derive(Clone, Debug)]
enum Ty {
    Unknown,
    Def(usize),
    /// A type outside the crate (of another crate, a primitive, a type parameter, `impl Trait`
    /// or `dyn Trait`), which has no inherent method of the crate.
    Foreign,
    /// A standard type that holds others: `Option`, `Result`, `Seq` (vectors, slices and
    /// arrays), `Map`, `Iter` and `Tuple`, with the types it holds.
    Std(&'static str, Vec<Text>),
}

struct Builder<'a> {
    files: &'a [(String, String)],
    by_path: HashMap<&'a str, usize>,
    modules: Vec<Module<'a>>,
    bindings: Vec<Binding<'a>>,
    paths: Vec<Path<'a>>,
    /// Whether each file has been reached.
    reached: Vec<bool>,
    /// The `mod name;` declarations a `#[path]` attribute places, as `file:line`.
    placed: Vec<String>,
    /// For each file: its tokens, the matching brackets, what its braces open, and its module.
    toks: Vec<Vec<(Tok<'a>, usize)>>,
    mates: Vec<Vec<usize>>,
    opens: Vec<HashMap<usize, Opening>>,
    fns: Vec<FnRec<'a>>,
    impls: Vec<ImplRec>,
    defs: Vec<Def<'a>>,
    def_of: HashMap<(usize, &'a str), usize>,
    fn_of: HashMap<(usize, &'a str), usize>,
    /// The names of the type parameters declared anywhere in the crate.
    generic: HashSet<&'a str>,
}

/// A file to read: the file, and its parent module and name there, or none for a crate root.
type Todo<'a> = (usize, Option<(usize, &'a str)>);

/// Fields, each with the tokens of its type.
type Fields<'a> = Vec<(Field<'a>, (usize, usize))>;

/// The token at `k`, if any.
fn tok<'a>(toks: &[(Tok<'a>, usize)], k: usize) -> Option<Tok<'a>> {
    toks.get(k).map(|t| t.0)
}

/// The position after the `<…>` that opens at `k`, stepping over bracketed groups.
fn after_angle(toks: &[(Tok<'_>, usize)], mate: &[usize], mut k: usize) -> usize {
    let mut depth = 0usize;
    while let Some(t) = tok(toks, k) {
        match t {
            Tok::Lt => depth += 1,
            Tok::Gt => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return k + 1;
                }
            }
            Tok::LParen | Tok::LBrack | Tok::Open => k = mate[k],
            Tok::Semi | Tok::Close => return k,
            _ => {}
        }
        k += 1;
    }
    k
}

/// The visibility written before the `fn` at `at`, as the path of the module it opens the
/// function to, from the function's own module (see `FnRec::vis`).
fn visibility<'a>(toks: &[(Tok<'a>, usize)], mate: &[usize], at: usize) -> Vec<&'a str> {
    let mut k = at;
    // Back past `const`, `async`, `unsafe` and `extern "C"` (whose string makes no token).
    while k > 0
        && matches!(
            toks[k - 1].0,
            Tok::Ident("const" | "async" | "unsafe" | "extern") | Tok::Str
        )
    {
        k -= 1;
    }
    match k.checked_sub(1).map(|p| toks[p].0) {
        Some(Tok::Ident("pub")) => vec!["crate"],
        Some(Tok::RParen) if mate[k - 1] > 0 && toks[mate[k - 1] - 1].0 == Tok::Ident("pub") => {
            let inside: Vec<&str> = toks[mate[k - 1] + 1..k - 1]
                .iter()
                .filter_map(|t| match t.0 {
                    Tok::Ident(w) if w != "in" => Some(w),
                    _ => None,
                })
                .collect();
            match inside.as_slice() {
                ["self"] => Vec::new(),
                _ => inside,
            }
        }
        _ => Vec::new(),
    }
}

/// The fields of the struct or variant whose body opens at `k`, `{ name: T, … }` or
/// `(T, …)`, each with the tokens of its type; none for any other token.
fn field_list<'a>(toks: &[(Tok<'a>, usize)], mate: &[usize], k: usize) -> Fields<'a> {
    let mut fields = Vec::new();
    match tok(toks, k) {
        Some(Tok::Open) => {
            for (s, e) in parts(toks, mate, k + 1, mate[k]) {
                let s = past_attrs(toks, mate, s, e);
                if let (Some(Tok::Ident(f)), Some(Tok::Colon)) = (tok(toks, s), tok(toks, s + 1)) {
                    fields.push((Field::Named(f), (s + 2, e)));
                }
            }
        }
        Some(Tok::LParen) => {
            for (n, (s, e)) in parts(toks, mate, k + 1, mate[k]).into_iter().enumerate() {
                fields.push((Field::Pos(n), (past_attrs(toks, mate, s, e), e)));
            }
        }
        _ => {}
    }
    fields
}

/// The position of the end of the expression going on at `k`: the `,` or `;` after it, or the
/// bracket that closes the group it is in. Bracketed groups are stepped over.
fn expr_end(toks: &[(Tok<'_>, usize)], mate: &[usize], mut k: usize) -> usize {
    while let Some(t) = tok(toks, k) {
        match t {
            Tok::Comma | Tok::Semi | Tok::Close | Tok::RParen | Tok::RBrack => return k,
            Tok::Open | Tok::LParen | Tok::LBrack => k = mate[k],
            _ => {}
        }
        k += 1;
    }
    k
}

/// The first position in `k..end` whose token is `want`, stepping over bracketed groups, before
/// any `;` or closing bracket of the group `k` is in.
fn find(
    toks: &[(Tok<'_>, usize)],
    mate: &[usize],
    mut k: usize,
    end: usize,
    want: Tok<'_>,
) -> Option<usize> {
    while k < end {
        let t = tok(toks, k)?;
        if t == want {
            return Some(k);
        }
        match t {
            Tok::Semi | Tok::Close | Tok::RParen | Tok::RBrack => return None,
            Tok::Open | Tok::LParen | Tok::LBrack => k = mate[k],
            _ => {}
        }
        k += 1;
    }
    None
}

/// The parts of `toks[s..e]` between the commas outside brackets and `<…>`.
fn parts(toks: &[(Tok<'_>, usize)], mate: &[usize], s: usize, e: usize) -> Vec<(usize, usize)> {
    let (mut out, mut from, mut depth, mut k) = (Vec::new(), s, 0usize, s);
    while k < e {
        match toks[k].0 {
            Tok::LParen | Tok::LBrack | Tok::Open => k = mate[k],
            Tok::Lt => depth += 1,
            Tok::Gt => depth = depth.saturating_sub(1),
            Tok::Comma if depth == 0 => {
                out.push((from, k));
                from = k + 1;
            }
            _ => {}
        }
        k += 1;
    }
    if from < e {
        out.push((from, e));
    }
    out
}

/// The start of `toks[s..e]` past attributes and a visibility.
fn past_attrs(toks: &[(Tok<'_>, usize)], mate: &[usize], mut s: usize, e: usize) -> usize {
    while s < e {
        match (tok(toks, s), tok(toks, s + 1)) {
            (Some(Tok::Hash), Some(Tok::LBrack)) | (Some(Tok::Ident("pub")), Some(Tok::LParen)) => {
                s = mate[s + 1] + 1;
            }
            (Some(Tok::Ident("pub")), _) => s += 1,
            _ => break,
        }
    }
    s.min(e)
}

/// The position of the `;` that ends the statement going on at `k`, stepping over bracketed
/// groups, or of the bracket that closes the group it is in.
fn to_semi(toks: &[(Tok<'_>, usize)], mate: &[usize], mut k: usize) -> usize {
    while let Some(t) = tok(toks, k) {
        match t {
            Tok::Semi | Tok::Close | Tok::RParen | Tok::RBrack => return k,
            Tok::Open | Tok::LParen | Tok::LBrack => k = mate[k],
            _ => {}
        }
        k += 1;
    }
    k
}

/// The name the identifier at `k` binds if it is in a pattern: a lower-case word that is no
/// keyword, no call, no path segment and no field.
fn binder<'a>(toks: &[(Tok<'a>, usize)], k: usize) -> Option<&'a str> {
    let Some(Tok::Ident(w)) = tok(toks, k) else {
        return None;
    };
    let lower = w.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') && w != "_";
    let next = tok(toks, k + 1);
    let before = k.checked_sub(1).and_then(|p| tok(toks, p));
    (lower
        && !KEYWORDS.contains(&w)
        && !matches!(next, Some(Tok::LParen | Tok::Open | Tok::Sep | Tok::Bang))
        && !matches!(before, Some(Tok::Sep | Tok::Dot)))
    .then_some(w)
}

/// Whether the brace at `k` opens the fields of a struct pattern, after a type's name.
fn struct_pattern(toks: &[(Tok<'_>, usize)], k: usize) -> bool {
    k > 0
        && matches!(toks[k - 1].0, Tok::Ident(w) if w.starts_with(|c: char| c.is_ascii_uppercase()))
}

/// Adds to `out` the type parameters the generic items of `toks` declare: the names first in
/// each part of the `<…>` after `impl` or after the name of a `fn`, `struct`, `enum`,
/// `union`, `trait` or `type`.
fn generic_names<'a>(toks: &[(Tok<'a>, usize)], mate: &[usize], out: &mut HashSet<&'a str>) {
    for k in 1..toks.len() {
        let declares = toks[k].0 == Tok::Lt
            && (toks[k - 1].0 == Tok::Ident("impl")
                || (k > 1
                    && matches!(toks[k - 1].0, Tok::Ident(_))
                    && matches!(
                        toks[k - 2].0,
                        Tok::Ident("fn" | "struct" | "enum" | "union" | "trait" | "type")
                    )));
        if !declares {
            continue;
        }
        let close = after_angle(toks, mate, k).saturating_sub(1);
        for (s, _) in parts(toks, mate, k + 1, close) {
            let s = s + usize::from(tok(toks, s) == Some(Tok::Ident("const")));
            if let Some(Tok::Ident(name)) = tok(toks, s) {
                out.insert(name);
            }
        }
    }
}

/// Whether the `let` at `i` is a statement binding one name, `let [mut] x [: T] [= e];`.
fn simple_let(toks: &[(Tok<'_>, usize)], i: usize) -> bool {
    let starts = i == 0
        || matches!(
            tok(toks, i - 1),
            Some(Tok::Semi | Tok::Open | Tok::Close | Tok::RBrack)
        );
    let k = i + 1 + usize::from(tok(toks, i + 1) == Some(Tok::Ident("mut")));
    starts
        && matches!(tok(toks, k), Some(Tok::Ident(_)))
        && matches!(tok(toks, k + 1), Some(Tok::Colon | Tok::Eq | Tok::Semi))
}

/// Whether the `|` at `i` opens the parameters of a closure.
fn closure_start(toks: &[(Tok<'_>, usize)], i: usize) -> bool {
    i == 0
        || matches!(
            tok(toks, i - 1),
            Some(
                Tok::LParen
                    | Tok::Comma
                    | Tok::Eq
                    | Tok::Open
                    | Tok::Semi
                    | Tok::FatArrow
                    | Tok::Colon
                    | Tok::Ident("move" | "return")
            )
        )
}

impl<'a> Builder<'a> {
    /// Reads every file the crate roots reach, from the roots down.
    fn new(files: &'a [(String, String)]) -> Result<Builder<'a>, String> {
        let by_path: HashMap<&str, usize> = files
            .iter()
            .enumerate()
            .map(|(i, (p, _))| (p.as_str(), i))
            .collect();
        let n = files.len();
        let mut b = Builder {
            files,
            by_path,
            modules: Vec::new(),
            bindings: Vec::new(),
            paths: Vec::new(),
            reached: vec![false; n],
            placed: Vec::new(),
            toks: vec![Vec::new(); n],
            mates: vec![Vec::new(); n],
            opens: vec![HashMap::new(); n],
            fns: Vec::new(),
            impls: Vec::new(),
            defs: Vec::new(),
            def_of: HashMap::new(),
            fn_of: HashMap::new(),
            generic: HashSet::new(),
        };
        let mut todo: Vec<Todo<'a>> = files
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, (p, _))| {
                p == "lib.rs"
                    || p == "main.rs"
                    || p.strip_prefix("bin/").is_some_and(|r| !r.contains('/'))
            })
            .map(|(i, _)| (i, None))
            .collect();
        while let Some((file, parent)) = todo.pop() {
            if !b.reached[file] {
                b.reached[file] = true;
                b.read(file, parent, &mut todo)?;
            }
        }
        Ok(b)
    }

    /// Reads `file` as a module under `parent` (a crate root when `None`), and queues the files
    /// its `mod name;` declarations name.
    fn read(
        &mut self,
        file: usize,
        parent: Option<(usize, &'a str)>,
        todo: &mut Vec<Todo<'a>>,
    ) -> Result<(), String> {
        let files = self.files;
        let (path, text) = (files[file].0.as_str(), files[file].1.as_str());
        let stem = path.strip_suffix(".rs").unwrap_or(path);
        // A crate root and a `mod.rs` read their declarations from their own directory, any
        // other file from the directory of its own name.
        let dir = if parent.is_none() || path == "mod.rs" || path.ends_with("/mod.rs") {
            path.rsplit_once('/').map_or("", |(d, _)| d)
        } else {
            stem
        };
        let top = self.module(file, parent.map(|p| p.0), dir.to_string());
        if let Some((p, name)) = parent {
            self.modules[p].children.insert(name, top);
        }
        let toks = lex(text);
        let mate = mates(&toks);
        generic_names(&toks, &mate, &mut self.generic);
        let mut opens: HashMap<usize, Opening> = HashMap::new();
        // What the braces open around the current token opened, and the modules open,
        // innermost last.
        let (mut braces, mut scopes): (Vec<Opening>, Vec<usize>) = (Vec::new(), vec![top]);
        // Whether a `#[path = "…"]` attribute is open before the next item: the `mod name;` it
        // precedes names a file the attribute places, which is not read.
        let mut path_attr = false;
        let mut i = 0;
        while let Some(&(t, line)) = toks.get(i) {
            let here = *scopes.last().expect("the file's own module stays open");
            let item_level = braces
                .last()
                .is_none_or(|o| matches!(o, Opening::Module(_)));
            let in_impl = match braces.last() {
                Some(&Opening::Impl(id)) => Some(id),
                _ => None,
            };
            let after_sep = i > 0 && toks[i - 1].0 == Tok::Sep;
            let (all, at) = (&toks, i);
            let next = move |k: usize| tok(all, at + k);
            i += 1;
            if t == Tok::Ident("path")
                && at > 0
                && toks[at - 1].0 == Tok::LBrack
                && next(1) == Some(Tok::Eq)
            {
                path_attr = true;
            }
            match t {
                Tok::Open => braces.push(opens.get(&at).copied().unwrap_or(Opening::Other)),
                Tok::Semi => path_attr = false,
                Tok::Close => {
                    if matches!(braces.pop(), Some(Opening::Module(_))) {
                        scopes.pop();
                    }
                }
                // `use<'a>` is a bound, not a declaration.
                Tok::Ident("use")
                    if matches!(
                        next(1),
                        Some(Tok::Ident(_) | Tok::Sep | Tok::Open | Tok::Star)
                    ) =>
                {
                    i = self.use_tree(&toks, i, here);
                }
                Tok::Ident("mod") => {
                    let (Some(Tok::Ident(name)), Some(after)) = (next(1), next(2)) else {
                        continue;
                    };
                    let d = &self.modules[here].dir;
                    let sub = |rest: &str| {
                        if d.is_empty() {
                            rest.to_string()
                        } else {
                            format!("{d}/{rest}")
                        }
                    };
                    if after == Tok::Open {
                        path_attr = false;
                        let inner = self.module(file, Some(here), sub(name));
                        self.modules[here].children.insert(name, inner);
                        opens.insert(at + 2, Opening::Module(inner));
                        braces.push(Opening::Module(inner));
                        scopes.push(inner);
                        i += 2;
                    } else if after == Tok::Semi {
                        if std::mem::take(&mut path_attr) {
                            self.placed.push(format!("{path}:{line}"));
                            self.modules[here].placed.insert(name);
                            i += 2;
                            continue;
                        }
                        let at = |p: String| self.by_path.get(p.as_str()).copied();
                        let child = at(sub(&format!("{name}.rs")))
                            .or_else(|| at(sub(&format!("{name}/mod.rs"))))
                            .ok_or_else(|| format!("{path}:{line}: `mod {name};` names no file"))?;
                        todo.push((child, Some((here, name))));
                        i += 2;
                    }
                }
                // An `impl` block, not `impl Trait` in a type.
                Tok::Ident("impl")
                    if at == 0
                        || matches!(
                            toks[at - 1].0,
                            Tok::Semi | Tok::Open | Tok::Close | Tok::RBrack | Tok::Ident("unsafe")
                        ) =>
                {
                    if let Some(open) = self.impl_header(&toks, &mate, at, file, here) {
                        opens.insert(open, Opening::Impl(self.impls.len() - 1));
                    }
                }
                Tok::Ident("fn") => {
                    let Some(Tok::Ident(name)) = next(1) else {
                        continue;
                    };
                    if item_level {
                        self.modules[here].items.insert(name);
                    }
                    if let Some((id, open)) = self.fn_header(&toks, &mate, at, file, here, in_impl)
                    {
                        opens.insert(open, Opening::Fn(id));
                        if item_level {
                            self.fn_of.entry((here, name)).or_insert(id);
                        }
                        if let Some(imp) = in_impl {
                            self.impls[imp].methods.push(id);
                        }
                    }
                }
                Tok::Ident("type") if in_impl.is_some() => {
                    if let (Some(imp), Some(Tok::Ident("Target")), Some(Tok::Eq)) =
                        (in_impl, next(1), next(2))
                    {
                        self.impls[imp].target = Some((at + 3, to_semi(&toks, &mate, at + 3)));
                    }
                }
                Tok::Ident("macro_rules") if item_level => {
                    if let (Some(Tok::Bang), Some(Tok::Ident(name))) = (next(1), next(2)) {
                        self.modules[here].items.insert(name);
                    }
                }
                Tok::Ident(word) if item_level && ITEMS.contains(&word) => {
                    if let Some(Tok::Ident(name)) = next(1) {
                        self.modules[here].items.insert(name);
                        if matches!(word, "struct" | "enum" | "union" | "type") {
                            self.def(&toks, &mate, at, (file, here), word, name);
                        }
                    }
                }
                Tok::Ident(first)
                    if !after_sep
                        && next(1) == Some(Tok::Sep)
                        && matches!(next(2), Some(Tok::Ident(_))) =>
                {
                    let mut segs = vec![first];
                    let mut last = line;
                    while let (Some(&(Tok::Sep, _)), Some(&(Tok::Ident(s), l))) =
                        (toks.get(i), toks.get(i + 1))
                    {
                        segs.push(s);
                        last = l;
                        i += 2;
                    }
                    self.paths.push(Path {
                        module: here,
                        segs,
                        line: last,
                    });
                }
                _ => {}
            }
        }
        self.toks[file] = toks;
        self.mates[file] = mate;
        self.opens[file] = opens;
        Ok(())
    }

    /// Records the `impl` block whose keyword is at `at`, and gives the position of its brace.
    fn impl_header(
        &mut self,
        toks: &[(Tok<'a>, usize)],
        mate: &[usize],
        at: usize,
        file: usize,
        module: usize,
    ) -> Option<usize> {
        let mut k = at + 1;
        if tok(toks, k)? == Tok::Lt {
            k = after_angle(toks, mate, k);
        }
        k += usize::from(tok(toks, k)? == Tok::Bang);
        let start = k;
        let (mut depth, mut trait_end) = (0usize, None);
        loop {
            match tok(toks, k)? {
                Tok::Lt => depth += 1,
                Tok::Gt => depth = depth.saturating_sub(1),
                Tok::LParen | Tok::LBrack => k = mate[k],
                Tok::Ident("for") if depth == 0 && trait_end.is_none() => trait_end = Some(k),
                Tok::Ident("where") | Tok::Open if depth == 0 => break,
                Tok::Semi | Tok::Close => return None,
                _ => {}
            }
            k += 1;
        }
        let end = k;
        while tok(toks, k)? != Tok::Open {
            k += 1;
        }
        let (ty, deref) = match trait_end {
            Some(f) => {
                // The trait's name is its path's last segment before any `<`.
                let name = toks[start..f]
                    .iter()
                    .take_while(|t| t.0 != Tok::Lt)
                    .filter_map(|t| match t.0 {
                        Tok::Ident(w) => Some(w),
                        _ => None,
                    })
                    .last();
                ((f + 1, end), name == Some("Deref"))
            }
            None => ((start, end), false),
        };
        self.impls.push(ImplRec {
            file,
            module,
            ty,
            inherent: trait_end.is_none(),
            deref,
            target: None,
            methods: Vec::new(),
            def: None,
        });
        Some(k)
    }

    /// Records the function whose keyword is at `at` if it has a body, and gives it and the
    /// position of the body's brace.
    fn fn_header(
        &mut self,
        toks: &[(Tok<'a>, usize)],
        mate: &[usize],
        at: usize,
        file: usize,
        module: usize,
        imp: Option<usize>,
    ) -> Option<(usize, usize)> {
        let Tok::Ident(name) = tok(toks, at + 1)? else {
            return None;
        };
        let mut k = at + 2;
        if tok(toks, k)? == Tok::Lt {
            k = after_angle(toks, mate, k);
        }
        if tok(toks, k)? != Tok::LParen {
            return None;
        }
        let params = (k, mate[k]);
        let first = parts(toks, mate, k + 1, mate[k]).into_iter().next();
        let method = first.is_some_and(|(s, e)| (s..e).any(|j| toks[j].0 == Tok::Ident("self")));
        k = mate[k] + 1;
        let mut ret = None;
        if tok(toks, k)? == Tok::Arrow {
            let (s, mut depth) = (k + 1, 0usize);
            k = s;
            while let Some(t) = tok(toks, k) {
                match t {
                    Tok::Lt => depth += 1,
                    Tok::Gt => depth = depth.saturating_sub(1),
                    Tok::LParen | Tok::LBrack => k = mate[k],
                    Tok::Ident("where") | Tok::Open | Tok::Semi if depth == 0 => break,
                    _ => {}
                }
                k += 1;
            }
            ret = Some((s, k));
        }
        loop {
            match tok(toks, k)? {
                Tok::Open => break,
                Tok::Semi | Tok::Close => return None,
                _ => k += 1,
            }
        }
        self.fns.push(FnRec {
            file,
            module,
            name,
            imp,
            params,
            method,
            ret,
            vis: visibility(toks, mate, at),
        });
        Some((self.fns.len() - 1, k))
    }

    /// Records the struct, enum, union or type alias whose keyword `word` is at `at`, named
    /// `name`, in `(file, module)`.
    fn def(
        &mut self,
        toks: &[(Tok<'a>, usize)],
        mate: &[usize],
        at: usize,
        (file, module): (usize, usize),
        word: &str,
        name: &'a str,
    ) {
        let mut k = at + 2;
        if tok(toks, k) == Some(Tok::Lt) {
            k = after_angle(toks, mate, k);
        }
        let (mut fields, mut alias, mut variants) = (Vec::new(), None, HashMap::new());
        if word == "type" {
            while tok(toks, k).is_some_and(|t| !matches!(t, Tok::Eq | Tok::Semi)) {
                k += 1;
            }
            if tok(toks, k) == Some(Tok::Eq) {
                alias = Some((k + 1, to_semi(toks, mate, k + 1)));
            }
        } else {
            while tok(toks, k).is_some_and(|t| !matches!(t, Tok::Open | Tok::LParen | Tok::Semi)) {
                k += 1;
            }
            if word != "enum" {
                fields = field_list(toks, mate, k);
            } else if tok(toks, k) == Some(Tok::Open) {
                for (s, e) in parts(toks, mate, k + 1, mate[k]) {
                    let s = past_attrs(toks, mate, s, e);
                    if let Some(Tok::Ident(v)) = tok(toks, s).filter(|_| s < e) {
                        variants.insert(v, field_list(toks, mate, s + 1));
                    }
                }
            }
        }
        self.def_of.entry((module, name)).or_insert(self.defs.len());
        self.defs.push(Def {
            file,
            module,
            name,
            fields,
            alias,
            variants,
            methods: HashMap::new(),
            deref: None,
        });
    }

    fn module(&mut self, file: usize, parent: Option<usize>, dir: String) -> usize {
        let root = parent.map_or(self.modules.len(), |p| self.modules[p].root);
        self.modules.push(Module {
            file,
            parent,
            root,
            dir,
            children: HashMap::new(),
            items: HashSet::new(),
            bound: HashMap::new(),
            globs: Vec::new(),
            placed: HashSet::new(),
        });
        self.modules.len() - 1
    }

    /// Reads the tree of a `use` declaration from `i`, just after the keyword, into bindings of
    /// `module`, and gives the position after its `;`. The tree's braces are kept on a stack.
    fn use_tree(&mut self, toks: &[(Tok<'a>, usize)], mut i: usize, module: usize) -> usize {
        // `use ::name` names another crate: its tokens are read past and bind nothing here.
        let outside = tok(toks, i) == Some(Tok::Sep);
        let mut path: Vec<&'a str> = Vec::new();
        // The length of the path before each open brace of the tree.
        let mut bases = vec![0];
        let (mut alias, mut glob, mut pending, mut after_as, mut line) =
            (None, false, false, false, 0);
        while let Some(&(t, l)) = toks.get(i) {
            i += 1;
            match t {
                Tok::Ident("as") => after_as = true,
                Tok::Ident(s) if after_as => {
                    alias = Some(s);
                    after_as = false;
                }
                Tok::Ident(s) => {
                    path.push(s);
                    (pending, line) = (true, l);
                }
                Tok::Star => (glob, pending, line) = (true, true, l),
                Tok::Open => {
                    bases.push(path.len());
                    pending = false;
                }
                Tok::Comma | Tok::Close | Tok::Semi => {
                    if pending && !outside {
                        self.bind(module, &path, alias, glob, line);
                    }
                    (alias, glob, pending) = (None, false, false);
                    if t == Tok::Close {
                        bases.pop();
                    }
                    if t == Tok::Semi {
                        break;
                    }
                    path.truncate(bases.last().copied().unwrap_or(0));
                }
                _ => {}
            }
        }
        i
    }

    /// Records the leaf `path` of a `use` tree in `module`, bound to `alias` or its last segment
    /// unless it is a glob or bound to `_`.
    fn bind(
        &mut self,
        module: usize,
        path: &[&'a str],
        alias: Option<&'a str>,
        glob: bool,
        line: usize,
    ) {
        let mut segs = path.to_vec();
        if !glob && segs.last() == Some(&"self") {
            segs.pop();
        }
        let id = self.bindings.len();
        let name = alias.or_else(|| segs.last().copied());
        if glob {
            self.modules[module].globs.push(id);
        } else if let Some(name) = name.filter(|&n| n != "_") {
            self.modules[module].bound.entry(name).or_insert(id);
        }
        self.bindings.push(Binding {
            module,
            segs,
            glob,
            line,
        });
    }

    /// Resolves `segs` from `*pos`, at `*at`, as far as the resolved bindings `done` allow; a
    /// glob import being resolved (`blocked`) is passed over. With `value`, the path is written
    /// in code, so its last segment is an item rather than a module of the same name: Rust keeps
    /// the two in separate namespaces.
    fn advance(
        &self,
        segs: &[&'a str],
        pos: &mut usize,
        at: &mut Res<'a>,
        done: &[Option<Res<'a>>],
        blocked: &[bool],
        value: bool,
    ) -> Step<'a> {
        loop {
            let (Some(&seg), Res::Module(x)) = (segs.get(*pos), *at) else {
                return Step::Done(*at);
            };
            let module = &self.modules[x];
            let last = value && *pos + 1 == segs.len();
            let child = module.children.get(seg).map(|&c| Res::Module(c));
            *at = match seg {
                "crate" if *pos == 0 => Res::Module(module.root),
                "self" => Res::Module(x),
                "super" => module.parent.map_or(Res::Outside, Res::Module),
                _ => {
                    let mut found = if last { None } else { child };
                    if found.is_none() && module.placed.contains(seg) {
                        found = Some(Res::Outside);
                    }
                    if found.is_none() && module.items.contains(seg) {
                        found = Some(Res::Item(x, seg));
                    }
                    if let (None, Some(&b)) = (found, module.bound.get(seg)) {
                        match done[b] {
                            Some(r) => found = Some(r),
                            None => return Step::Need(b),
                        }
                    }
                    if found.is_none() && last {
                        found = child;
                    }
                    if found.is_none() {
                        match self.through_globs(x, seg, done, blocked) {
                            Ok(r) => found = r,
                            Err(b) => return Step::Need(b),
                        }
                    }
                    match found {
                        Some(r) => r,
                        // Another crate, a local name or a type parameter.
                        None if *pos == 0 => Res::Outside,
                        // A name a macro brings in (see the module comment).
                        None => Res::Item(x, seg),
                    }
                }
            };
            *pos += 1;
        }
    }

    /// The name `seg` as one of the glob imports of module `x` brings it in, or the binding to
    /// resolve first.
    // Complexity tradeoff: one hash lookup per glob import of the module, rather than a table
    // merged from the names of every module a glob reaches, which costs the size of those
    // modules for each glob. A module has a few glob imports (at most 3 here), and Rust's own
    // resolution takes the same steps.
    fn through_globs(
        &self,
        x: usize,
        seg: &'a str,
        done: &[Option<Res<'a>>],
        blocked: &[bool],
    ) -> Result<Option<Res<'a>>, usize> {
        for &g in &self.modules[x].globs {
            if blocked.get(g) == Some(&true) {
                continue;
            }
            let t = match done[g] {
                Some(Res::Module(t)) => t,
                // An enum's variants, or something outside: no module item.
                Some(_) => continue,
                None => return Err(g),
            };
            let m = &self.modules[t];
            if let Some(&c) = m.children.get(seg) {
                return Ok(Some(Res::Module(c)));
            }
            if m.items.contains(seg) {
                return Ok(Some(Res::Item(t, seg)));
            }
            if let Some(&b) = m.bound.get(seg) {
                return done[b].map(Some).ok_or(b);
            }
        }
        Ok(None)
    }

    /// What `segs`, written in code in `module`, names, and how many of its segments that used.
    fn resolve(
        &self,
        module: usize,
        segs: &[&'a str],
        done: &[Option<Res<'a>>],
    ) -> (Res<'a>, usize) {
        let (mut pos, mut at) = (0, Res::Module(module));
        match self.advance(segs, &mut pos, &mut at, done, &[], true) {
            Step::Done(r) => (r, pos),
            Step::Need(_) => (Res::Outside, pos),
        }
    }

    /// The type `text` names. An alias is followed, each once; a wrapper of `THROUGH` is seen
    /// through. A loop, not recursion: each turn reads a shorter span or follows an alias.
    ///
    /// A type parameter is outside the crate where it is declared, since only trait methods can
    /// be called on it there; but where an item's type is read for a use of the item
    /// (`given`: a field of a value, a function's return at its call) the parameter stands for
    /// the type given, which may be the crate's, so it is not known.
    fn ty_of(&self, mut text: Text, done: &[Option<Res<'a>>], given: bool) -> Ty {
        let mut followed: HashSet<usize> = HashSet::new();
        loop {
            let (toks, mate) = (&self.toks[text.file], &self.mates[text.file]);
            let (mut s, e) = text.span;
            while s < e
                && matches!(
                    toks[s].0,
                    Tok::Amp | Tok::Life | Tok::Star | Tok::Ident("mut" | "const")
                )
            {
                s += 1;
            }
            match tok(toks, s).filter(|_| s < e) {
                Some(Tok::LBrack) => {
                    let close = mate[s].min(e);
                    let mut k = s + 1;
                    while k < close && toks[k].0 != Tok::Semi {
                        if matches!(toks[k].0, Tok::LParen | Tok::LBrack | Tok::Open) {
                            k = mate[k];
                        }
                        k += 1;
                    }
                    let span = (s + 1, k.min(close));
                    return Ty::Std("Seq", vec![Text { span, ..text }]);
                }
                Some(Tok::LParen) => {
                    let close = mate[s].min(e);
                    let held = parts(toks, mate, s + 1, close);
                    return Ty::Std(
                        "Tuple",
                        held.into_iter().map(|span| Text { span, ..text }).collect(),
                    );
                }
                Some(Tok::Ident(_)) => {}
                _ => return Ty::Unknown,
            }
            let mut segs = Vec::new();
            let mut k = s;
            while let (true, Some(Tok::Ident(w))) = (k < e, tok(toks, k)) {
                segs.push(w);
                k += 1;
                if k + 1 < e && tok(toks, k) == Some(Tok::Sep) {
                    k += 1;
                } else {
                    break;
                }
            }
            let args: Vec<Text> = if k < e && toks[k].0 == Tok::Lt {
                let close = after_angle(toks, mate, k).saturating_sub(1).min(e);
                parts(toks, mate, k + 1, close)
                    .into_iter()
                    .filter(|&(a, _)| toks[a].0 != Tok::Life)
                    .map(|span| Text { span, ..text })
                    .collect()
            } else {
                Vec::new()
            };
            if segs == ["Self"] {
                return text.self_def.map_or(Ty::Unknown, Ty::Def);
            }
            if matches!(segs.first(), Some(&("dyn" | "impl" | "fn"))) {
                return Ty::Foreign;
            }
            if let Some(d) = self.def_at(text.module, &segs, done) {
                let def = &self.defs[d];
                match def.alias {
                    None => return Ty::Def(d),
                    Some(span) if followed.insert(d) => {
                        text = Text {
                            file: def.file,
                            span,
                            module: def.module,
                            self_def: None,
                        };
                        continue;
                    }
                    Some(_) => return Ty::Unknown,
                }
            }
            let last = segs.last().copied().unwrap_or("");
            if THROUGH.contains(&last) {
                match args.first() {
                    Some(&inner) => {
                        text = inner;
                        continue;
                    }
                    None => return Ty::Unknown,
                }
            }
            let kind = match last {
                "Option" => "Option",
                "Result" => "Result",
                "Vec" | "VecDeque" | "SmallVec" | "BinaryHeap" => "Seq",
                "HashMap" | "BTreeMap" | "IndexMap" => "Map",
                // A name no module of the crate gives: another crate's, a primitive or a type
                // parameter. An associated type (`Self::Out`, `T::Item`) may be the crate's.
                _ => {
                    let first = segs.first().copied().unwrap_or("");
                    if first == "Self"
                        || (self.generic.contains(first) && (given || segs.len() > 1))
                    {
                        return Ty::Unknown;
                    }
                    return match self.resolve(text.module, &segs, done) {
                        (Res::Outside, _) => Ty::Foreign,
                        _ => Ty::Unknown,
                    };
                }
            };
            return Ty::Std(kind, args);
        }
    }

    /// The definition `segs` names, written in `module`.
    fn def_at(&self, module: usize, segs: &[&'a str], done: &[Option<Res<'a>>]) -> Option<usize> {
        match self.resolve(module, segs, done) {
            (Res::Item(m, name), pos) if pos == segs.len() => self.def_of.get(&(m, name)).copied(),
            _ => None,
        }
    }

    /// Resolves every binding, then every path, finds the type of each `impl` block and the
    /// calls of methods written apart from their types, and gives the graph.
    fn finish(mut self) -> Result<Graph, String> {
        let n = self.bindings.len();
        let mut done: Vec<Option<Res<'a>>> = vec![None; n];
        let mut state: Vec<(usize, Res<'a>)> = self
            .bindings
            .iter()
            .map(|x| (0, Res::Module(x.module)))
            .collect();
        let mut on_stack = vec![false; n];
        // Each binding is pushed once and its path is advanced, never restarted, so the whole
        // is linear in the segments of the bindings.
        for start in 0..n {
            if done[start].is_some() {
                continue;
            }
            let mut stack = vec![start];
            on_stack[start] = true;
            while let Some(&x) = stack.last() {
                let (mut pos, mut at) = state[x];
                let segs = &self.bindings[x].segs;
                let step = self.advance(segs, &mut pos, &mut at, &done, &on_stack, false);
                state[x] = (pos, at);
                let result = match step {
                    Step::Need(y) if !on_stack[y] => {
                        on_stack[y] = true;
                        stack.push(y);
                        continue;
                    }
                    // Rust rejects a cycle of bindings by name; it leads outside the graph.
                    Step::Need(_) => Res::Outside,
                    Step::Done(r) => r,
                };
                done[x] = Some(result);
                on_stack[x] = false;
                stack.pop();
            }
        }
        let mut found = Found::default();
        for (x, binding) in self.bindings.iter().enumerate() {
            let from = self.modules[binding.module].file;
            let to = match done[x] {
                Some(Res::Item(m, _)) => self.modules[m].file,
                Some(Res::Module(m)) if binding.glob => self.modules[m].file,
                _ => continue,
            };
            found.add(from, to, binding.line, || binding.segs.join("::"));
        }
        for path in &self.paths {
            // Every binding is resolved by now, so the path resolves to its end.
            if let (Res::Item(m, _), _) = self.resolve(path.module, &path.segs, &done) {
                let from = self.modules[path.module].file;
                found.add(from, self.modules[m].file, path.line, || {
                    path.segs.join("::")
                });
            }
        }
        let open = self.openings(&done);
        let mut loose = self.attach(&done, &open);
        let mut split: HashMap<&'a str, Vec<(usize, usize)>> = HashMap::new();
        for def in &self.defs {
            for (&name, fs) in &def.methods {
                // Only a method with `self` is called as `x.name(…)`; an associated function
                // is called by its path, whose import `Walk::member` draws.
                for &f in fs.iter().filter(|&&f| self.fns[f].method) {
                    let file = self.fns[f].imp.map_or(def.file, |m| self.impls[m].file);
                    if file != def.file {
                        split.entry(name).or_default().push((file, open[f]));
                    }
                }
            }
        }
        for (&name, files) in &loose {
            split.entry(name).or_default().extend(files);
        }
        for files in loose.values_mut() {
            files.sort_unstable();
            files.dedup();
        }
        let span = self.spans();
        for files in split.values_mut() {
            files.sort_unstable();
            files.dedup();
        }
        let mut unknown = 0;
        for file in 0..self.files.len() {
            if !self.reached[file] {
                continue;
            }
            let mut walk = Walk::new(&self, &done, (&split, &loose, &span), file);
            walk.run();
            unknown += walk.unknown;
            for (to, line, call) in walk.out {
                found.add(file, to, line, || call);
            }
        }
        // The files reached are numbered in path order.
        let mut number = vec![usize::MAX; self.files.len()];
        let mut files = Vec::new();
        for (f, (path, _)) in self.files.iter().enumerate() {
            if self.reached[f] {
                number[f] = files.len();
                files.push(path.clone());
            }
        }
        let mut imports: Vec<Vec<(usize, Cite)>> = vec![Vec::new(); files.len()];
        for ((from, to), cite) in found.0 {
            imports[number[from]].push((number[to], cite));
        }
        for list in &mut imports {
            list.sort_unstable_by_key(|&(g, _)| g);
        }
        let loose_impls = self
            .impls
            .iter()
            .filter(|m| m.inherent && m.def.is_none())
            .count();
        Ok(Graph {
            undeclared: self.files.len() - files.len(),
            placed: self.placed,
            files,
            imports,
            unknown_calls: unknown,
            loose_impls,
        })
    }

    /// For each function, the module its visibility opens it to.
    fn openings(&self, done: &[Option<Res<'a>>]) -> Vec<usize> {
        self.fns
            .iter()
            .map(|f| {
                let (mut pos, mut at) = (0, Res::Module(f.module));
                match self.advance(&f.vis, &mut pos, &mut at, done, &[], false) {
                    Step::Done(Res::Module(m)) => m,
                    _ => self.modules[f.module].root,
                }
            })
            .collect()
    }

    /// For each module, its number in a walk of the module tree from the roots and the number
    /// after its last descendant, so a module lies within another exactly when its number lies
    /// within the other's span. An explicit stack; each module is entered once.
    fn spans(&self) -> Vec<(usize, usize)> {
        let n = self.modules.len();
        let mut kids: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (m, module) in self.modules.iter().enumerate() {
            if let Some(p) = module.parent {
                kids[p].push(m);
            }
        }
        let mut span = vec![(0, 0); n];
        let mut count = 0;
        // Each entry is a module and whether its descendants are done.
        let mut stack: Vec<(usize, bool)> = (0..n)
            .filter(|&m| self.modules[m].parent.is_none())
            .map(|m| (m, false))
            .collect();
        while let Some((m, finished)) = stack.pop() {
            if finished {
                span[m].1 = count;
                continue;
            }
            span[m].0 = count;
            count += 1;
            stack.push((m, true));
            stack.extend(kids[m].iter().map(|&k| (k, false)));
        }
        span
    }

    /// Finds the type of each `impl` block and gives each type its inherent methods and its
    /// `Deref` target. Gives the methods of the inherent blocks whose type is not found, by
    /// name, each with the files of those blocks.
    fn attach(&mut self, done: &[Option<Res<'a>>], open: &[usize]) -> Calls<'a> {
        let mut loose: Calls<'a> = HashMap::new();
        for m in 0..self.impls.len() {
            let imp = &self.impls[m];
            let text = Text {
                file: imp.file,
                span: imp.ty,
                module: imp.module,
                self_def: None,
            };
            let def = match self.ty_of(text, done, false) {
                Ty::Def(d) => Some(d),
                _ => None,
            };
            self.impls[m].def = def;
            let imp = &self.impls[m];
            match def {
                Some(d) if imp.inherent => {
                    for &f in &imp.methods {
                        let name = self.fns[f].name;
                        self.defs[d].methods.entry(name).or_default().push(f);
                    }
                }
                Some(d) if imp.deref => {
                    self.defs[d].deref = imp.target.map(|span| Text {
                        file: imp.file,
                        span,
                        module: imp.module,
                        self_def: Some(d),
                    });
                }
                None if imp.inherent => {
                    for &f in &imp.methods {
                        loose
                            .entry(self.fns[f].name)
                            .or_default()
                            .push((imp.file, open[f]));
                    }
                }
                _ => {}
            }
        }
        loose
    }
}

/// The methods written apart from their types, by name, each with the file it is written in and
/// the module its visibility opens it to.
type Calls<'a> = HashMap<&'a str, Vec<(usize, usize)>>;

/// Names bound together, each with its type.
type Binds<'a> = Vec<(&'a str, Ty)>;

/// The imports found, each pair of files with the first place it is written.
#[derive(Default)]
struct Found(HashMap<(usize, usize), Cite>);

impl Found {
    fn add(&mut self, from: usize, to: usize, line: usize, path: impl FnOnce() -> String) {
        if from == to {
            return;
        }
        let earlier = self.0.get(&(from, to)).is_some_and(|c| c.line <= line);
        if !earlier {
            let path = path();
            self.0.insert((from, to), Cite { line, path });
        }
    }
}

/// What the code around a token is in: its module, the type `Self` names, and the function body
/// (its braces and the length of the scope log when it opened).
#[derive(Clone, Copy)]
struct Frame {
    module: usize,
    self_def: Option<usize>,
    body: Option<(usize, usize)>,
    scope: usize,
}

/// The pass over one file's code that types the receivers of method calls, and draws an import
/// for each call of a method written apart from its type (see the module comment).
struct Walk<'b, 'a> {
    b: &'b Builder<'a>,
    done: &'b [Option<Res<'a>>],
    /// The methods written apart from their types, by name, each with the files they are
    /// written in; and those of the `impl` blocks whose type is not found.
    split: &'b Calls<'a>,
    loose: &'b Calls<'a>,
    /// The span of each module in the module tree (`Builder::spans`).
    span: &'b [(usize, usize)],
    file: usize,
    toks: &'b [(Tok<'a>, usize)],
    mate: &'b [usize],
    /// The names to bind when the brace at a position opens (a `for` loop's, a block's).
    at_open: HashMap<usize, Binds<'a>>,
    /// The names to bind from a position to another (a `match` arm's, a closure's, an
    /// `if let`'s), by the first position.
    ranges: HashMap<usize, Vec<(Binds<'a>, usize)>>,
    /// Where bound ranges end, each with the length of the log to go back to there.
    ends: HashMap<usize, usize>,
    /// The types of the parameters of a closure given to a standard method, by its first `|`.
    closure_params: HashMap<usize, Vec<Ty>>,
    /// The locals in scope by name, innermost last, each with the body it belongs to; and the
    /// names in the order they were bound, so a closing brace unbinds them.
    locals: HashMap<&'a str, Vec<(usize, Ty)>>,
    log: Vec<&'a str>,
    frames: Vec<Frame>,
    /// The `.` of each method call typed from its receiver.
    typed: Vec<bool>,
    /// The first word of each chain typed, so a chain a `let` typed is not typed again.
    chained: Vec<bool>,
    /// The types read, by the text they were read from.
    read: HashMap<(Text, bool), Ty>,
    out: Vec<(usize, usize, String)>,
    unknown: usize,
}

impl<'b, 'a> Walk<'b, 'a> {
    fn new(
        b: &'b Builder<'a>,
        done: &'b [Option<Res<'a>>],
        (split, loose, span): (&'b Calls<'a>, &'b Calls<'a>, &'b [(usize, usize)]),
        file: usize,
    ) -> Walk<'b, 'a> {
        let (toks, mate) = (&b.toks[file][..], &b.mates[file][..]);
        let top = b
            .modules
            .iter()
            .position(|m| m.file == file)
            .expect("a file read is a module");
        Walk {
            b,
            done,
            split,
            loose,
            span,
            file,
            toks,
            mate,
            at_open: HashMap::new(),
            ranges: HashMap::new(),
            ends: HashMap::new(),
            closure_params: HashMap::new(),
            locals: HashMap::new(),
            log: Vec::new(),
            frames: vec![Frame {
                module: top,
                self_def: None,
                body: None,
                scope: 0,
            }],
            typed: vec![false; toks.len()],
            chained: vec![false; toks.len()],
            read: HashMap::new(),
            out: Vec::new(),
            unknown: 0,
        }
    }

    fn tok(&self, k: usize) -> Option<Tok<'a>> {
        tok(self.toks, k)
    }

    fn frame(&self) -> Frame {
        *self.frames.last().expect("the file's frame stays")
    }

    /// One pass over the tokens: braces open and close scopes, a `let` binds a local when its
    /// statement ends, and each chain of calls is typed from its first word.
    fn run(&mut self) {
        let mut pending: Vec<(usize, &'a str, Ty)> = Vec::new();
        let mut i = 0;
        while let Some(t) = self.tok(i) {
            if let Some(mark) = self.ends.remove(&i) {
                self.unbind(mark);
            }
            for (names, end) in self.ranges.remove(&i).unwrap_or_default() {
                let mark = self.log.len();
                for (name, ty) in names {
                    self.bind(name, ty);
                }
                let at = self.ends.entry(end).or_insert(mark);
                *at = (*at).min(mark);
            }
            while let Some((_, name, ty)) = pending.pop_if(|p| p.0 < i) {
                self.bind(name, ty);
            }
            match t {
                Tok::Open => self.enter(i),
                Tok::Close => self.leave(),
                Tok::Ident("let") => pending.extend(self.let_stmt(i)),
                Tok::Ident("for") if self.tok(i + 1) != Some(Tok::Lt) => self.for_loop(i),
                Tok::Ident("match") => self.match_arms(i),
                Tok::Pipe if closure_start(self.toks, i) => self.closure(i),
                Tok::Ident(_)
                    if !self.chained[i]
                        && !matches!(
                            i.checked_sub(1).and_then(|p| self.tok(p)),
                            Some(Tok::Dot | Tok::Sep)
                        ) =>
                {
                    self.chain(i);
                }
                Tok::Num(_) | Tok::Str if !self.chained[i] => {
                    self.value(i);
                }
                // A method called on what no chain types: `(a + b).m()`, a block, a literal.
                Tok::Dot if !self.typed[i] => {
                    if let Some(Tok::Ident(name)) = self.tok(i + 1)
                        && self.tok(self.after_name(i + 1)) == Some(Tok::LParen)
                    {
                        self.call(Ty::Unknown, name, self.toks[i + 1].1);
                    }
                }
                _ => {}
            }
            i += 1;
        }
    }

    /// The position after the name at `k` and its turbofish, if any.
    fn after_name(&self, k: usize) -> usize {
        if self.tok(k + 1) == Some(Tok::Sep) && self.tok(k + 2) == Some(Tok::Lt) {
            after_angle(self.toks, self.mate, k + 2)
        } else {
            k + 1
        }
    }

    fn enter(&mut self, i: usize) {
        let mut f = Frame {
            scope: self.log.len(),
            ..self.frame()
        };
        match self.b.opens[self.file].get(&i) {
            Some(&Opening::Module(m)) => {
                (f.module, f.self_def, f.body) = (m, None, None);
            }
            Some(&Opening::Impl(id)) => f.self_def = self.b.impls[id].def,
            Some(&Opening::Fn(id)) => {
                f.self_def = self.b.fns[id].imp.and_then(|m| self.b.impls[m].def);
                f.body = Some((i, self.mate[i]));
                self.frames.push(f);
                self.params(id);
                return;
            }
            _ => {}
        }
        self.frames.push(f);
        for (name, ty) in self.at_open.remove(&i).unwrap_or_default() {
            self.bind(name, ty);
        }
    }

    fn leave(&mut self) {
        if self.frames.len() > 1 {
            let f = self.frames.pop().expect("more than one");
            self.unbind(f.scope);
        }
    }

    /// Unbinds the names bound since the log had length `mark`.
    fn unbind(&mut self, mark: usize) {
        while self.log.len() > mark {
            let name = self.log.pop().expect("longer than the mark");
            if let Some(list) = self.locals.get_mut(name) {
                list.pop();
            }
        }
    }

    fn bind(&mut self, name: &'a str, ty: Ty) {
        let Some((open, _)) = self.frame().body else {
            return;
        };
        self.locals.entry(name).or_default().push((open, ty));
        self.log.push(name);
    }

    /// The type of the local `name` in the current body; none if no local has the name.
    fn local(&self, name: &str) -> Option<Ty> {
        let (open, _) = self.frame().body?;
        match self.locals.get(name)?.last() {
            Some((o, ty)) if *o == open => Some(ty.clone()),
            _ => None,
        }
    }

    /// The type `text` names where an item is used (see `Builder::ty_of`).
    fn ty(&mut self, text: Text) -> Ty {
        self.ty_in(text, true)
    }

    fn ty_in(&mut self, text: Text, given: bool) -> Ty {
        // Complexity tradeoff: a type is read once per text and kept, so a long return type is
        // not read again at every call of its function.
        if let Some(ty) = self.read.get(&(text, given)) {
            return ty.clone();
        }
        let ty = self.b.ty_of(text, self.done, given);
        self.read.insert((text, given), ty.clone());
        ty
    }

    /// A type written at `span` in the current module.
    fn here(&mut self, span: (usize, usize)) -> Ty {
        let f = self.frame();
        let text = Text {
            file: self.file,
            span,
            module: f.module,
            self_def: f.self_def,
        };
        self.ty_in(text, false)
    }

    /// Binds the parameters of function `id`.
    fn params(&mut self, id: usize) {
        let (lp, rp) = self.b.fns[id].params;
        for (s, e) in parts(self.toks, self.mate, lp + 1, rp) {
            let s = past_attrs(self.toks, self.mate, s, e);
            let colon = (s..e).find(|&k| self.toks[k].0 == Tok::Colon);
            let pattern = s..colon.unwrap_or(e);
            if pattern
                .clone()
                .any(|k| self.toks[k].0 == Tok::Ident("self"))
            {
                let ty = match colon {
                    Some(c) => self.here((c + 1, e)),
                    None => self.frame().self_def.map_or(Ty::Unknown, Ty::Def),
                };
                self.bind("self", ty);
                continue;
            }
            let k = s + usize::from(self.tok(s) == Some(Tok::Ident("mut")));
            match (colon, self.tok(k)) {
                (Some(c), Some(Tok::Ident(x))) if k + 1 == c => {
                    let ty = self.here((c + 1, e));
                    self.bind(x, ty);
                }
                _ => {
                    let ty = colon.map_or(Ty::Unknown, |c| self.here((c + 1, e)));
                    for (x, ty) in self.pattern(s, pattern.end, ty) {
                        self.bind(x, ty);
                    }
                }
            }
        }
    }

    /// The locals the `let` at `i` binds after its statement, each with the end of the statement
    /// and its type. The names of a `let` in the condition of an `if` or `while` are bound over
    /// the rest of the condition and the block instead.
    fn let_stmt(&mut self, i: usize) -> Vec<(usize, &'a str, Ty)> {
        if simple_let(self.toks, i) {
            return self.simple_let(i).into_iter().collect();
        }
        let (toks, mate) = (self.toks, self.mate);
        let cond = i > 0 && matches!(toks[i - 1].0, Tok::Ident("if" | "while") | Tok::Amp);
        let mut end = i + 1;
        loop {
            match tok(toks, end) {
                Some(Tok::Colon | Tok::Eq | Tok::Semi) => break,
                Some(Tok::LParen | Tok::LBrack) => end = mate[end],
                Some(Tok::Open) if struct_pattern(toks, end) => end = mate[end],
                Some(Tok::Open | Tok::Close) | None => return Vec::new(),
                _ => {}
            }
            end += 1;
        }
        let (ty, stop) = match toks[end].0 {
            Tok::Colon => {
                let e = find(toks, mate, end + 1, usize::MAX, Tok::Eq)
                    .unwrap_or_else(|| to_semi(toks, mate, end + 1));
                (self.here((end + 1, e)), to_semi(toks, mate, e))
            }
            Tok::Eq => {
                let (ty, stop) = self.value(end + 1);
                let fits = match tok(toks, stop) {
                    Some(Tok::Open | Tok::Amp) => cond,
                    Some(Tok::Semi | Tok::Ident("else")) => !cond,
                    _ => false,
                };
                (if fits { ty } else { Ty::Unknown }, stop)
            }
            _ => (Ty::Unknown, end),
        };
        let names = self.pattern(i + 1, end, ty);
        if cond {
            if let Some(open) = find(toks, mate, stop, usize::MAX, Tok::Open) {
                self.ranges
                    .entry(stop.max(i + 1))
                    .or_default()
                    .push((names, mate[open]));
            }
            return Vec::new();
        }
        let semi = to_semi(toks, mate, stop);
        names.into_iter().map(|(x, ty)| (semi, x, ty)).collect()
    }

    /// The local the `let` of one name at `i` binds, with the end of its statement and its type.
    fn simple_let(&mut self, i: usize) -> Option<(usize, &'a str, Ty)> {
        let k = i + 1 + usize::from(self.tok(i + 1) == Some(Tok::Ident("mut")));
        let Tok::Ident(name) = self.tok(k)? else {
            return None;
        };
        let end = to_semi(self.toks, self.mate, k + 1);
        let ty = match self.tok(k + 1)? {
            Tok::Colon => {
                let mut e = k + 2;
                while e < end && self.toks[e].0 != Tok::Eq {
                    if matches!(self.toks[e].0, Tok::LParen | Tok::LBrack | Tok::Open) {
                        e = self.mate[e];
                    }
                    e += 1;
                }
                self.here((k + 2, e.min(end)))
            }
            Tok::Eq => match self.value(k + 2) {
                (ty, stop) if stop == end => ty,
                _ => Ty::Unknown,
            },
            _ => Ty::Unknown,
        };
        Some((end, name, ty))
    }

    /// Types the value that starts at `i` (past `&`, `*` and `mut`), when it is a chain or a
    /// literal, and gives its type and the position after its chain.
    fn value(&mut self, mut i: usize) -> (Ty, usize) {
        while matches!(self.tok(i), Some(Tok::Amp | Tok::Star | Tok::Ident("mut"))) {
            i += 1;
        }
        match self.tok(i) {
            Some(Tok::Ident(w)) if !KEYWORDS.contains(&w) || w == "self" || w == "Self" => {
                self.chain(i)
            }
            Some(Tok::Num(_) | Tok::Str) => {
                self.chained[i] = true;
                self.postfix(Ty::Foreign, i + 1)
            }
            _ => (Ty::Unknown, i),
        }
    }

    /// The type of an element of the collection or iterator `ty`.
    fn elem(&mut self, ty: &Ty) -> Ty {
        match ty {
            Ty::Std("Iter" | "Seq" | "Option", args) => {
                args.first().copied().map_or(Ty::Unknown, |t| self.ty(t))
            }
            Ty::Std("Map" | "Pairs", args) if args.len() == 2 => Ty::Std("Pair", args.clone()),
            Ty::Std("Enumerate", args) => Ty::Std("Indexed", args.clone()),
            _ => Ty::Unknown,
        }
    }

    /// The types of the parameters of a closure given first to the standard method `name`
    /// called on `ty`; none when not known.
    fn closure_types(&mut self, ty: &Ty, name: &str) -> Vec<Ty> {
        match (ty, name) {
            (
                Ty::Std("Iter" | "Pairs" | "Enumerate", _),
                "map" | "filter" | "filter_map" | "flat_map" | "for_each" | "any" | "all" | "find"
                | "find_map" | "position" | "take_while" | "skip_while" | "map_while" | "inspect"
                | "max_by_key" | "min_by_key" | "partition" | "try_for_each" | "is_sorted_by_key",
            )
            | (
                Ty::Std("Seq", _),
                "retain"
                | "retain_mut"
                | "sort_by_key"
                | "sort_unstable_by_key"
                | "sort_by_cached_key"
                | "binary_search_by"
                | "binary_search_by_key"
                | "partition_point",
            ) => vec![self.elem(ty)],
            (Ty::Std("Iter" | "Pairs" | "Enumerate", _), "max_by" | "min_by")
            | (Ty::Std("Seq", _), "sort_by" | "sort_unstable_by" | "dedup_by") => {
                let e = self.elem(ty);
                vec![e.clone(), e]
            }
            (Ty::Std("Map", args), "retain") if args.len() == 2 => {
                vec![self.ty(args[0]), self.ty(args[1])]
            }
            (
                Ty::Std("Option", args),
                "map" | "and_then" | "is_some_and" | "is_none_or" | "filter" | "inspect"
                | "take_if",
            )
            | (Ty::Std("Result", args), "map" | "and_then" | "inspect" | "is_ok_and") => {
                vec![args.first().copied().map_or(Ty::Unknown, |t| self.ty(t))]
            }
            (Ty::Std("Result", args), "map_err" | "or_else" | "is_err_and" | "inspect_err") => {
                vec![args.get(1).copied().map_or(Ty::Unknown, |t| self.ty(t))]
            }
            _ => Vec::new(),
        }
    }

    /// The types of the parts of a tuple of type `ty` with `n` parts.
    fn tuple_parts(&mut self, ty: &Ty, n: usize) -> Vec<Ty> {
        match ty {
            Ty::Std("Tuple" | "Pair", args) if args.len() == n => {
                args.clone().into_iter().map(|t| self.ty(t)).collect()
            }
            Ty::Std("Indexed", args) if n == 2 => {
                vec![
                    Ty::Foreign,
                    args.first().copied().map_or(Ty::Unknown, |t| self.ty(t)),
                ]
            }
            _ => vec![Ty::Unknown; n],
        }
    }

    /// The definition and variant a pattern's path `toks[s..e]` names, if any: a struct, or an
    /// enum and one of its variants.
    fn pattern_def(&self, s: usize, e: usize) -> Option<(usize, Option<&'a str>)> {
        let mut segs = Vec::new();
        let mut k = s;
        while k < e {
            match self.toks[k].0 {
                Tok::Ident(w) => segs.push(w),
                Tok::Sep => {}
                Tok::Lt => k = after_angle(self.toks, self.mate, k) - 1,
                _ => return None,
            }
            k += 1;
        }
        let f = self.frame();
        if segs.first() == Some(&"Self") {
            return match segs.len() {
                1 => f.self_def.map(|d| (d, None)),
                2 => f.self_def.map(|d| (d, Some(segs[1]))),
                _ => None,
            };
        }
        match self.b.resolve(f.module, &segs, self.done) {
            (Res::Item(m, name), pos) if pos == segs.len() => {
                self.b.def_of.get(&(m, name)).map(|&d| (d, None))
            }
            (Res::Item(m, name), pos) if pos + 1 == segs.len() => {
                self.b.def_of.get(&(m, name)).map(|&d| (d, Some(segs[pos])))
            }
            _ => None,
        }
    }

    /// The fields of the struct or variant a pattern names, each with its type; none when the
    /// path names neither.
    fn pattern_fields(&mut self, path: (usize, usize)) -> Option<Vec<(Field<'a>, Ty)>> {
        let (d, variant) = self.pattern_def(path.0, path.1)?;
        let def = &self.b.defs[d];
        let fields = match variant {
            None => &def.fields,
            Some(v) => def.variants.get(v)?,
        };
        let texts: Vec<(Field<'a>, Text)> = fields
            .iter()
            .map(|&(f, span)| {
                let text = Text {
                    file: def.file,
                    span,
                    module: def.module,
                    self_def: Some(d),
                };
                (f, text)
            })
            .collect();
        Some(texts.into_iter().map(|(f, t)| (f, self.ty(t))).collect())
    }

    /// The names the pattern `toks[s..e]` binds, each with its type when the pattern's value is
    /// of type `ty`. Names in a part of the pattern not followed are bound with no type, so
    /// they hide any local of the same name. An explicit stack of parts.
    fn pattern(&mut self, s: usize, e: usize, ty: Ty) -> Binds<'a> {
        let (toks, mate) = (self.toks, self.mate);
        let mut out = Vec::new();
        let mut todo = vec![(s, e, ty)];
        while let Some((mut s, e, ty)) = todo.pop() {
            while s < e
                && matches!(
                    toks[s].0,
                    Tok::Amp | Tok::Pipe | Tok::Ident("mut" | "ref" | "box")
                )
            {
                s += 1;
            }
            if s >= e {
                continue;
            }
            // The first of the alternatives `p | q`, whose names are those of each.
            let e = find(toks, mate, s, e, Tok::Pipe).unwrap_or(e);
            let last = mate[e - 1];
            match (toks[s].0, tok(toks, s + 1)) {
                (Tok::Ident(_), Some(Tok::Other)) if s + 1 < e => {
                    if let Some(x) = binder(toks, s) {
                        out.push((x, ty.clone()));
                    }
                    todo.push((s + 2, e, ty));
                }
                (Tok::Ident(_), _) if s + 1 == e => {
                    if let Some(x) = binder(toks, s) {
                        out.push((x, ty));
                    }
                }
                (Tok::LParen, _) if last == s => {
                    let ps = parts(toks, mate, s + 1, e - 1);
                    let tys = if ps.len() == 1 && toks[e - 2].0 != Tok::Comma {
                        vec![ty]
                    } else {
                        self.tuple_parts(&ty, ps.len())
                    };
                    self.push_parts(&ps, tys, &mut todo);
                }
                (Tok::LBrack, _) if last == s => {
                    let el = self.held(&ty, &["Seq"], 0);
                    let ps = parts(toks, mate, s + 1, e - 1);
                    let tys = vec![el; ps.len()];
                    self.push_parts(&ps, tys, &mut todo);
                }
                _ if matches!(toks[e - 1].0, Tok::RParen | Tok::Close) && last > s => {
                    let path = (s, last);
                    let inner = parts(toks, mate, last + 1, e - 1);
                    let name = match toks[last - 1].0 {
                        Tok::Ident(w) => w,
                        _ => "",
                    };
                    let fields = match (toks[last].0, name) {
                        (Tok::LParen, "Some" | "Ok") if last == s + 1 => Some(vec![(
                            Field::Pos(0),
                            self.held(&ty, &["Option", "Result"], 0),
                        )]),
                        (Tok::LParen, "Err") if last == s + 1 => {
                            Some(vec![(Field::Pos(0), self.held(&ty, &["Result"], 1))])
                        }
                        _ => self.pattern_fields(path),
                    }
                    .unwrap_or_default();
                    let field = |f: Field<'_>| {
                        fields
                            .iter()
                            .find(|(g, _)| *g == f)
                            .map_or(Ty::Unknown, |(_, t)| t.clone())
                    };
                    if toks[last].0 == Tok::LParen {
                        let tys = (0..inner.len()).map(|n| field(Field::Pos(n))).collect();
                        self.push_parts(&inner, tys, &mut todo);
                    } else {
                        for (a, b) in inner {
                            let a = past_attrs(toks, mate, a, b);
                            let named = (a..b).find(|&k| {
                                matches!(toks[k].0, Tok::Ident(w) if !matches!(w, "ref" | "mut" | "box"))
                            });
                            let Some(at) = named else {
                                continue;
                            };
                            let Tok::Ident(f) = toks[at].0 else {
                                continue;
                            };
                            let fty = field(Field::Named(f));
                            match tok(toks, at + 1).filter(|_| at + 1 < b) {
                                Some(Tok::Colon) => todo.push((at + 2, b, fty)),
                                _ => todo.push((at, at + 1, fty)),
                            }
                        }
                    }
                }
                _ => {
                    for k in s..e {
                        if let Some(x) = binder(toks, k) {
                            out.push((x, Ty::Unknown));
                        }
                    }
                }
            }
        }
        out
    }

    /// Queues each part of a tuple, slice or tuple-struct pattern with its type; a part with
    /// `..` in it (`rest @ ..`) gets no type.
    fn push_parts(&self, ps: &[(usize, usize)], tys: Vec<Ty>, todo: &mut Vec<(usize, usize, Ty)>) {
        let rest = |a: usize, b: usize| (a..b).any(|k| self.toks[k].0 == Tok::Dot);
        for (&(a, b), ty) in ps.iter().zip(tys) {
            todo.push((a, b, if rest(a, b) { Ty::Unknown } else { ty }));
        }
    }

    /// The `for` loop at `i`: its pattern's names are bound in its block.
    fn for_loop(&mut self, i: usize) {
        let (toks, mate) = (self.toks, self.mate);
        if i > 0
            && matches!(
                toks[i - 1].0,
                Tok::Ident(_) | Tok::Gt | Tok::RParen | Tok::RBrack
            )
        {
            return;
        }
        let mut k = i + 1;
        let at_in = loop {
            match tok(toks, k) {
                Some(Tok::Ident("in")) => break k,
                Some(Tok::LParen | Tok::LBrack) => k = mate[k],
                Some(Tok::Open) if struct_pattern(toks, k) => k = mate[k],
                Some(Tok::Open | Tok::Close | Tok::Semi) | None => return,
                _ => {}
            }
            k += 1;
        };
        let (ty, stop) = self.value(at_in + 1);
        let el = match (self.tok(at_in + 1), self.tok(stop), self.tok(stop + 1)) {
            (Some(Tok::Num(_)), _, _) | (_, Some(Tok::Dot), Some(Tok::Dot)) => Ty::Foreign,
            (_, Some(Tok::Open), _) => self.elem(&ty),
            _ => Ty::Unknown,
        };
        let Some(open) = find(toks, mate, stop, usize::MAX, Tok::Open)
            .or_else(|| (stop..toks.len()).find(|&k| toks[k].0 == Tok::Open))
        else {
            return;
        };
        let names = self.pattern(i + 1, at_in, el);
        self.at_open.entry(open).or_default().extend(names);
    }

    /// The `match` at `i`: each arm's names are bound from its guard to its end.
    fn match_arms(&mut self, i: usize) {
        let (toks, mate) = (self.toks, self.mate);
        let (ty, stop) = self.value(i + 1);
        let Some(open) = (stop..toks.len()).find(|&k| toks[k].0 == Tok::Open) else {
            return;
        };
        let ty = if open == stop { ty } else { Ty::Unknown };
        let close = mate[open];
        let mut s = open + 1;
        while s < close {
            let Some(arrow) = find(toks, mate, s, close, Tok::FatArrow) else {
                return;
            };
            let guard = find(toks, mate, s, arrow, Tok::Ident("if")).unwrap_or(arrow);
            let a = arrow + 1;
            let end = if tok(toks, a) == Some(Tok::Open) {
                mate[a] + 1
            } else {
                expr_end(toks, mate, a)
            };
            let names = self.pattern(s, guard, ty.clone());
            self.ranges
                .entry(guard)
                .or_default()
                .push((names, end.min(close)));
            s = end + usize::from(tok(toks, end) == Some(Tok::Comma));
        }
    }

    /// The closure whose parameters open at the `|` at `i`: its parameters are bound over its
    /// body.
    fn closure(&mut self, i: usize) {
        let (toks, mate) = (self.toks, self.mate);
        let mut k = i + 1;
        while let Some(t) = tok(toks, k) {
            match t {
                Tok::Pipe => break,
                Tok::LParen | Tok::LBrack | Tok::Open => k = mate[k],
                Tok::Semi | Tok::Close | Tok::RParen | Tok::RBrack => return,
                _ => {}
            }
            k += 1;
        }
        let c = k;
        let mut body = c + 1;
        if tok(toks, body) == Some(Tok::Arrow) {
            match (body..toks.len()).find(|&k| toks[k].0 == Tok::Open) {
                Some(o) => body = o,
                None => return,
            }
        }
        let end = if tok(toks, body) == Some(Tok::Open) {
            mate[body]
        } else {
            expr_end(toks, mate, body)
        };
        let given = self.closure_params.remove(&i).unwrap_or_default();
        let mut names = Vec::new();
        for (n, (s, e)) in parts(toks, mate, i + 1, c).into_iter().enumerate() {
            let colon = find(toks, mate, s, e, Tok::Colon);
            let ty = match colon {
                Some(c) => self.here((c + 1, e)),
                None => given.get(n).cloned().unwrap_or(Ty::Unknown),
            };
            names.extend(self.pattern(s, colon.unwrap_or(e), ty));
        }
        self.ranges.entry(c + 1).or_default().push((names, end));
    }

    /// Types the chain of calls, fields, `?` and indexing whose first word is at `i`, drawing
    /// the imports of its method calls, and gives its type and the position after it.
    fn chain(&mut self, i: usize) -> (Ty, usize) {
        self.chained[i] = true;
        let (ty, j) = self.primary(i);
        self.postfix(ty, j)
    }

    /// Types the calls, fields, `?` and indexing from `j` on a value of type `ty`.
    fn postfix(&mut self, mut ty: Ty, mut j: usize) -> (Ty, usize) {
        loop {
            match (self.tok(j), self.tok(j + 1)) {
                (Some(Tok::Dot), Some(Tok::Ident("await"))) => j += 2,
                (Some(Tok::Dot), Some(Tok::Ident(name))) => {
                    let k = self.after_name(j + 1);
                    if self.tok(k) == Some(Tok::LParen) {
                        let pipe = k + 1 + usize::from(self.tok(k + 1) == Some(Tok::Ident("move")));
                        if self.tok(pipe) == Some(Tok::Pipe) {
                            let params = self.closure_types(&ty, name);
                            if !params.is_empty() {
                                self.closure_params.insert(pipe, params);
                            }
                        }
                        self.typed[j] = true;
                        ty = self.call(ty, name, self.toks[j + 1].1);
                        j = self.mate[k] + 1;
                    } else {
                        ty = self.field(ty, Field::Named(name));
                        j += 2;
                    }
                }
                (Some(Tok::Dot), Some(Tok::Num(n))) => {
                    ty = match n.parse() {
                        Ok(p) => self.field(ty, Field::Pos(p)),
                        // `x.0.1`, read as one number.
                        Err(_) => Ty::Unknown,
                    };
                    j += 2;
                }
                (Some(Tok::Question), _) => {
                    ty = self.held(&ty, &["Option", "Result"], 0);
                    j += 1;
                }
                (Some(Tok::LBrack), _) => {
                    ty = match ty {
                        Ty::Std("Map", _) => self.held(&ty, &["Map"], 1),
                        _ => self.held(&ty, &["Seq"], 0),
                    };
                    j = self.mate[j] + 1;
                }
                _ => return (ty, j),
            }
        }
    }

    /// The type the standard type `ty` of one of `kinds` holds at `n`.
    fn held(&mut self, ty: &Ty, kinds: &[&str], n: usize) -> Ty {
        match ty {
            Ty::Std(kind, args) if kinds.contains(kind) => {
                args.get(n).copied().map_or(Ty::Unknown, |t| self.ty(t))
            }
            _ => Ty::Unknown,
        }
    }

    /// The type of the word or path at `i` and the position after it, and after the arguments
    /// when it is called. A path to a method (`Type::m`, `Self::m`) draws its import.
    fn primary(&mut self, i: usize) -> (Ty, usize) {
        let Some(Tok::Ident(first)) = self.tok(i) else {
            return (Ty::Unknown, i + 1);
        };
        let mut segs = vec![first];
        let mut j = i + 1;
        while self.tok(j) == Some(Tok::Sep) {
            match self.tok(j + 1) {
                Some(Tok::Ident(s)) => {
                    segs.push(s);
                    j += 2;
                }
                Some(Tok::Lt) => j = after_angle(self.toks, self.mate, j + 1),
                _ => break,
            }
        }
        let called = self.tok(j) == Some(Tok::LParen);
        let after = if called { self.mate[j] + 1 } else { j };
        if segs.len() == 1 {
            if self.tok(j) == Some(Tok::Bang) {
                // A macro: the pass reads its arguments as code.
                return (Ty::Unknown, j);
            }
            if let Some(ty) = self.local(first) {
                return (if called { Ty::Unknown } else { ty }, after);
            }
        }
        let f = self.frame();
        let line = self.toks[j - 1].1;
        let (def, member) = if first == "Self" {
            (f.self_def, segs.get(1).copied().filter(|_| segs.len() == 2))
        } else {
            match self.b.resolve(f.module, &segs, self.done) {
                (Res::Item(m, name), pos) if pos == segs.len() => {
                    match (self.b.def_of.get(&(m, name)), self.b.fn_of.get(&(m, name))) {
                        (Some(&d), _) => (Some(d), None),
                        (None, Some(&id)) if called => return (self.ret(id), after),
                        _ => return (Ty::Unknown, after),
                    }
                }
                (Res::Item(m, name), pos) if pos + 1 == segs.len() => {
                    (self.b.def_of.get(&(m, name)).copied(), Some(segs[pos]))
                }
                _ => return (Ty::Unknown, after),
            }
        };
        if first == "Self" && segs.len() > 2 {
            return (Ty::Unknown, after);
        }
        let Some(d) = def else {
            return (Ty::Unknown, after);
        };
        let ty = match member {
            None => Ty::Def(d),
            Some(m) => self.member(d, m, called, line),
        };
        (ty, after)
    }

    /// `Type::m` for the definition `d`: a method, whose import is drawn, or a variant.
    fn member(&mut self, d: usize, m: &'a str, called: bool, line: usize) -> Ty {
        let def = &self.b.defs[d];
        if let Some(fs) = def.methods.get(m) {
            let first = fs[0];
            for &f in fs {
                let to = self.b.fns[f].imp.map_or(def.file, |x| self.b.impls[x].file);
                self.edge(to, line, format!("{}::{m}", def.name));
            }
            return if called { self.ret(first) } else { Ty::Unknown };
        }
        self.loose_edges(m, line);
        if m.starts_with(|c: char| c.is_ascii_uppercase()) {
            Ty::Def(d)
        } else {
            Ty::Unknown
        }
    }

    /// The return type of function `id`.
    fn ret(&mut self, id: usize) -> Ty {
        let f = &self.b.fns[id];
        match f.ret {
            Some(span) => self.ty(Text {
                file: f.file,
                span,
                module: f.module,
                self_def: f.imp.and_then(|m| self.b.impls[m].def),
            }),
            None => Ty::Unknown,
        }
    }

    /// The call of method `name` on a value of type `ty`, and its type. A method written apart
    /// from its type draws the import of its file: exactly when the receiver's type is known,
    /// and of every file with a method of that name written apart from its type when not.
    fn call(&mut self, mut ty: Ty, name: &'a str, line: usize) -> Ty {
        let mut followed: HashSet<usize> = HashSet::new();
        loop {
            match ty {
                Ty::Def(d) => {
                    let def = &self.b.defs[d];
                    if let Some(fs) = def.methods.get(name) {
                        let first = fs[0];
                        if self.split.contains_key(name) {
                            for &f in fs {
                                let to =
                                    self.b.fns[f].imp.map_or(def.file, |x| self.b.impls[x].file);
                                self.edge(to, line, format!("{}::{name}", def.name));
                            }
                        }
                        return self.ret(first);
                    }
                    match def.deref {
                        Some(t) if followed.insert(d) => ty = self.ty(t),
                        _ => {
                            self.loose_edges(name, line);
                            return match name {
                                "clone" | "to_owned" | "borrow" | "borrow_mut" | "as_ref"
                                | "as_mut" | "lock" | "unwrap" | "expect" => Ty::Def(d),
                                _ => Ty::Unknown,
                            };
                        }
                    }
                }
                Ty::Std(kind, args) => return self.std_call(kind, args, name),
                Ty::Foreign => {
                    return match name {
                        "clone" | "to_owned" | "to_string" | "as_str" | "as_bytes" | "trim"
                        | "trim_start" | "trim_end" | "to_lowercase" | "to_uppercase" | "len"
                        | "is_empty" | "contains" | "starts_with" | "ends_with" => Ty::Foreign,
                        _ => Ty::Unknown,
                    };
                }
                Ty::Unknown => {
                    let split = self.split;
                    if self.edges_to(split, name, line) {
                        self.unknown += 1;
                    }
                    return Ty::Unknown;
                }
            }
        }
    }

    /// The import of every `impl` block whose type is not found and that has a method `name`.
    fn loose_edges(&mut self, name: &str, line: usize) {
        let loose = self.loose;
        self.edges_to(loose, name, line);
    }

    /// The import of each file of `calls` with a method `name` the current module may call, by
    /// its visibility; whether there is one.
    fn edges_to(&mut self, calls: &Calls<'a>, name: &str, line: usize) -> bool {
        let here = self.span[self.frame().module].0;
        let mut any = false;
        for &(to, open) in calls.get(name).map_or(&[][..], Vec::as_slice) {
            let (s, e) = self.span[open];
            if (s..e).contains(&here) {
                any = true;
                self.edge(to, line, format!("?.{name}"));
            }
        }
        any
    }

    /// The type of the standard method `name` called on the standard type `kind` holding `args`.
    fn std_call(&mut self, kind: &'static str, args: Vec<Text>, name: &str) -> Ty {
        let one =
            |k: &'static str, t: Option<&Text>| t.map_or(Ty::Unknown, |&t| Ty::Std(k, vec![t]));
        match (kind, name) {
            (
                "Option" | "Result",
                "unwrap" | "expect" | "unwrap_or" | "unwrap_or_default" | "unwrap_or_else"
                | "unwrap_unchecked",
            ) => args.first().copied().map_or(Ty::Unknown, |t| self.ty(t)),
            (
                _,
                "clone" | "as_ref" | "as_mut" | "as_deref" | "as_deref_mut" | "by_ref" | "to_owned"
                | "borrow" | "borrow_mut",
            ) => Ty::Std(kind, args),
            (
                "Seq",
                "first" | "last" | "get" | "get_mut" | "pop" | "first_mut" | "last_mut"
                | "pop_front" | "pop_back" | "front" | "back" | "front_mut" | "back_mut",
            ) => one("Option", args.first()),
            ("Seq", "iter" | "iter_mut" | "into_iter" | "drain") => one("Iter", args.first()),
            ("Map", "get" | "get_mut" | "remove") => one("Option", args.get(1)),
            ("Map", "values" | "values_mut" | "into_values") => one("Iter", args.get(1)),
            ("Map", "keys" | "into_keys") => one("Iter", args.first()),
            ("Map", "iter" | "iter_mut" | "into_iter" | "drain" | "range") => {
                Ty::Std("Pairs", args)
            }
            ("Option", "iter" | "into_iter") => one("Iter", args.first()),
            ("Iter", "enumerate") => Ty::Std("Enumerate", args),
            (
                "Pairs" | "Enumerate",
                "rev" | "skip" | "take" | "filter" | "peekable" | "skip_while" | "take_while"
                | "step_by" | "inspect" | "fuse",
            ) => Ty::Std(kind, args),
            (
                "Iter",
                "next" | "next_back" | "last" | "nth" | "find" | "max" | "min" | "max_by_key"
                | "min_by_key" | "max_by" | "min_by",
            ) => one("Option", args.first()),
            (
                "Iter",
                "rev" | "skip" | "take" | "filter" | "copied" | "cloned" | "peekable"
                | "skip_while" | "take_while" | "step_by" | "chain" | "inspect" | "fuse",
            ) => Ty::Std(kind, args),
            (
                _,
                "len" | "is_empty" | "contains" | "contains_key" | "count" | "is_some" | "is_none"
                | "is_ok" | "is_err" | "position" | "any" | "all",
            ) => Ty::Foreign,
            _ => Ty::Unknown,
        }
    }

    /// The type of field `field` of a value of type `ty`.
    fn field(&mut self, mut ty: Ty, field: Field<'_>) -> Ty {
        let mut followed: HashSet<usize> = HashSet::new();
        loop {
            match ty {
                Ty::Def(d) => {
                    let def = &self.b.defs[d];
                    if let Some(&(_, span)) = def.fields.iter().find(|(f, _)| *f == field) {
                        let text = Text {
                            file: def.file,
                            span,
                            module: def.module,
                            self_def: Some(d),
                        };
                        return self.ty(text);
                    }
                    match def.deref {
                        Some(t) if followed.insert(d) => ty = self.ty(t),
                        _ => return Ty::Unknown,
                    }
                }
                Ty::Std("Tuple" | "Pair", args) => {
                    return match field {
                        Field::Pos(n) => args.get(n).copied().map_or(Ty::Unknown, |t| self.ty(t)),
                        Field::Named(_) => Ty::Unknown,
                    };
                }
                Ty::Std("Indexed", args) => {
                    return match field {
                        Field::Pos(0) => Ty::Foreign,
                        Field::Pos(1) => args.first().copied().map_or(Ty::Unknown, |t| self.ty(t)),
                        _ => Ty::Unknown,
                    };
                }
                _ => return Ty::Unknown,
            }
        }
    }

    fn edge(&mut self, to: usize, line: usize, call: String) {
        if to != self.file {
            self.out.push((to, line, call));
        }
    }
}

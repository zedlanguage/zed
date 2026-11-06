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
//! file of the module or enum it names. A name a module neither declares nor binds by name (one a
//! glob or a macro brings in) is taken to be the module's own, so the edge goes to the module's
//! file, whose own imports then lead on to the defining file: the graph may hold a path through
//! an extra file in those two cases, but never misses a cycle. Paths into other crates (`std::`,
//! `zed_kernel::`) are no edges, so the edges of a binary root into its library are not drawn;
//! a library cannot import its binary, so they close no cycle.
//!
//! A cycle is a strongly connected component of two files or more (a file naming its own items
//! is no edge). Each is reported with its files, a shortest cycle through its first file, and
//! every import within it, each cited by file and line. The scan is one pass over the text, the
//! resolution one hash lookup per segment of a path, and the components are found by Tarjan's
//! algorithm with an explicit stack in O(n + e), n the bytes of the files and e the imports between
//! them. Sorting each file's imports, for the report and the citations, makes the whole
//! O(n + e log e) (COMPLEXITY F101).

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

/// A token of Rust text, as far as the import graph needs one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tok<'a> {
    Ident(&'a str),
    /// `::`
    Sep,
    Open,
    Close,
    Semi,
    Comma,
    Star,
    Bang,
    Other,
}

fn is_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c >= 0x80
}

/// The tokens of `text`, each with its line. Comments, string and character literals and
/// lifetimes are skipped, so a path written in them is not read as one.
fn lex(text: &str) -> Vec<(Tok<'_>, usize)> {
    let b = text.as_bytes();
    let (mut i, mut line) = (0, 1);
    let mut toks = Vec::new();
    while let Some(&c) = b.get(i) {
        match c {
            b'\n' => {
                line += 1;
                i += 1;
            }
            b' ' | b'\t' | b'\r' => i += 1,
            b'/' if b.get(i + 1) == Some(&b'/') => {
                while b.get(i).is_some_and(|&c| c != b'\n') {
                    i += 1;
                }
            }
            b'/' if b.get(i + 1) == Some(&b'*') => {
                let mut depth = 0usize;
                while i < b.len() {
                    if b[i..].starts_with(b"/*") {
                        depth += 1;
                        i += 2;
                    } else if b[i..].starts_with(b"*/") {
                        depth -= 1;
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        line += usize::from(b[i] == b'\n');
                        i += 1;
                    }
                }
            }
            b'"' => i = string(b, i, None, &mut line),
            b'\'' => i = quote(b, i, &mut line, &mut toks),
            b'0'..=b'9' => {
                i += 1;
                while b.get(i).is_some_and(|&c| {
                    is_ident(c) || (c == b'.' && b.get(i + 1).is_some_and(u8::is_ascii_digit))
                }) {
                    i += 1;
                }
            }
            c if is_ident(c) => {
                let start = i;
                while b.get(i).copied().is_some_and(is_ident) {
                    i += 1;
                }
                let word = &text[start..i];
                match (word, b.get(i)) {
                    ("r" | "br" | "cr", Some(b'#' | b'"')) => {
                        let hashes = b[i..].iter().take_while(|&&c| c == b'#').count();
                        if b.get(i + hashes) == Some(&b'"') {
                            i = string(b, i + hashes, Some(hashes), &mut line);
                        } else {
                            // A raw identifier, `r#type`: a name, not the keyword.
                            i += hashes;
                            while b.get(i).copied().is_some_and(is_ident) {
                                i += 1;
                            }
                            toks.push((Tok::Ident(&text[start..i]), line));
                        }
                    }
                    ("b" | "c", Some(b'"')) => i = string(b, i, None, &mut line),
                    // A byte literal `b'x'`: the quote that follows is read as a character.
                    ("b", Some(b'\'')) => {}
                    _ => toks.push((Tok::Ident(word), line)),
                }
            }
            _ => {
                let tok = match c {
                    b':' if b.get(i + 1) == Some(&b':') => {
                        i += 1;
                        Tok::Sep
                    }
                    b'{' => Tok::Open,
                    b'}' => Tok::Close,
                    b';' => Tok::Semi,
                    b',' => Tok::Comma,
                    b'*' => Tok::Star,
                    b'!' => Tok::Bang,
                    _ => Tok::Other,
                };
                toks.push((tok, line));
                i += 1;
            }
        }
    }
    toks
}

/// Skips the string literal whose opening quote is at `i`, raw with `hashes` when given, and
/// gives the position after it.
fn string(b: &[u8], mut i: usize, hashes: Option<usize>, line: &mut usize) -> usize {
    i += 1;
    while let Some(&c) = b.get(i) {
        *line += usize::from(c == b'\n');
        match (c, hashes) {
            (b'\\', None) => {
                *line += usize::from(b.get(i + 1) == Some(&b'\n'));
                i += 2;
            }
            (b'"', None) => return i + 1,
            (b'"', Some(h)) if b[i + 1..].iter().take(h).filter(|&&c| c == b'#').count() == h => {
                return i + 1 + h;
            }
            _ => i += 1,
        }
    }
    i
}

/// Skips the character literal or lifetime whose quote is at `i`, and gives the position after
/// it. A lifetime becomes a token of its own, so `'static` is not read as the word `static`.
fn quote<'a>(b: &[u8], i: usize, line: &mut usize, toks: &mut Vec<(Tok<'a>, usize)>) -> usize {
    if b.get(i + 1) == Some(&b'\\') {
        let mut j = i + 3;
        while b.get(j).is_some_and(|&c| c != b'\'') {
            j += 1;
        }
        return j + 1;
    }
    let width = match b.get(i + 1) {
        Some(&c) if c < 0x80 => 1,
        Some(&c) if c < 0xE0 => 2,
        Some(&c) if c < 0xF0 => 3,
        Some(_) => 4,
        None => return i + 1,
    };
    if b.get(i + 1 + width) == Some(&b'\'') {
        *line += usize::from(b[i + 1] == b'\n');
        return i + 2 + width;
    }
    let mut j = i + 1;
    while b.get(j).copied().is_some_and(is_ident) {
        j += 1;
    }
    toks.push((Tok::Other, *line));
    j
}

/// The keywords that begin an item whose name follows them.
const ITEMS: &[&str] = &[
    "fn", "struct", "enum", "union", "trait", "type", "const", "static",
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
enum Res {
    Module(usize),
    /// An item of the file.
    Item(usize),
    /// Something outside the crate, or a local name.
    Outside,
}

/// The progress of resolving a path.
enum Step {
    Done(Res),
    /// The path goes through a binding not yet resolved.
    Need(usize),
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
}

/// A file to read: the file, and its parent module and name there, or none for a crate root.
type Todo<'a> = (usize, Option<(usize, &'a str)>);

impl<'a> Builder<'a> {
    /// Reads every file the crate roots reach, from the roots down.
    fn new(files: &'a [(String, String)]) -> Result<Builder<'a>, String> {
        let by_path: HashMap<&str, usize> = files
            .iter()
            .enumerate()
            .map(|(i, (p, _))| (p.as_str(), i))
            .collect();
        let mut b = Builder {
            files,
            by_path,
            modules: Vec::new(),
            bindings: Vec::new(),
            paths: Vec::new(),
            reached: vec![false; files.len()],
            placed: Vec::new(),
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
        // The braces open around the current token, each with whether it opens a module, and
        // the modules open, innermost last.
        let (mut braces, mut scopes): (Vec<bool>, Vec<usize>) = (Vec::new(), vec![top]);
        // Whether a `#[path = "…"]` attribute is open before the next item: the `mod name;` it
        // precedes names a file the attribute places, which is not read.
        let mut path_attr = false;
        let mut i = 0;
        while let Some(&(tok, line)) = toks.get(i) {
            let here = *scopes.last().expect("the file's own module stays open");
            let item_level = braces.last().is_none_or(|&opens_module| opens_module);
            let after_sep = i > 0 && toks[i - 1].0 == Tok::Sep;
            let (all, at) = (&toks, i);
            let next = move |k: usize| all.get(at + k).map(|t| t.0);
            i += 1;
            if tok == Tok::Ident("path")
                && at > 0
                && toks[at - 1].0 == Tok::Other
                && next(1) == Some(Tok::Other)
            {
                path_attr = true;
            }
            match tok {
                Tok::Open => braces.push(false),
                Tok::Semi => path_attr = false,
                Tok::Close => {
                    if braces.pop() == Some(true) {
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
                        braces.push(true);
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
                Tok::Ident("macro_rules") if item_level => {
                    if let (Some(Tok::Bang), Some(Tok::Ident(name))) = (next(1), next(2)) {
                        self.modules[here].items.insert(name);
                    }
                }
                Tok::Ident(word) if item_level && ITEMS.contains(&word) => {
                    if let Some(Tok::Ident(name)) = next(1) {
                        self.modules[here].items.insert(name);
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
        Ok(())
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
            placed: HashSet::new(),
        });
        self.modules.len() - 1
    }

    /// Reads the tree of a `use` declaration from `i`, just after the keyword, into bindings of
    /// `module`, and gives the position after its `;`. The tree's braces are kept on a stack.
    fn use_tree(&mut self, toks: &[(Tok<'a>, usize)], mut i: usize, module: usize) -> usize {
        // `use ::name` names another crate: its tokens are read past and bind nothing here.
        let outside = toks.get(i).map(|t| t.0) == Some(Tok::Sep);
        let mut path: Vec<&'a str> = Vec::new();
        // The length of the path before each open brace of the tree.
        let mut bases = vec![0];
        let (mut alias, mut glob, mut pending, mut after_as, mut line) =
            (None, false, false, false, 0);
        while let Some(&(tok, l)) = toks.get(i) {
            i += 1;
            match tok {
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
                    if tok == Tok::Close {
                        bases.pop();
                    }
                    if tok == Tok::Semi {
                        break;
                    }
                    path.truncate(bases.last().copied().unwrap_or(0));
                }
                Tok::Sep | Tok::Bang | Tok::Other => {}
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
        let name = alias.or_else(|| segs.last().copied());
        if let Some(name) = name.filter(|&n| !glob && n != "_") {
            let id = self.bindings.len();
            self.modules[module].bound.entry(name).or_insert(id);
        }
        self.bindings.push(Binding {
            module,
            segs,
            glob,
            line,
        });
    }

    /// Resolves `segs` from `*pos`, at `*at`, as far as the resolved bindings `done` allow.
    fn advance(&self, segs: &[&str], pos: &mut usize, at: &mut Res, done: &[Option<Res>]) -> Step {
        loop {
            let (Some(&seg), Res::Module(x)) = (segs.get(*pos), *at) else {
                return Step::Done(*at);
            };
            let module = &self.modules[x];
            *at = match seg {
                "crate" if *pos == 0 => Res::Module(module.root),
                "self" => Res::Module(x),
                "super" => module.parent.map_or(Res::Outside, Res::Module),
                _ => {
                    if let Some(&c) = module.children.get(seg) {
                        Res::Module(c)
                    } else if module.placed.contains(seg) {
                        Res::Outside
                    } else if module.items.contains(seg) {
                        Res::Item(module.file)
                    } else if let Some(&b) = module.bound.get(seg) {
                        match done[b] {
                            Some(r) => r,
                            None => return Step::Need(b),
                        }
                    } else if *pos == 0 {
                        // Another crate, a local name or a type parameter.
                        Res::Outside
                    } else {
                        // A name a glob or a macro brings in (see the module comment).
                        Res::Item(module.file)
                    }
                }
            };
            *pos += 1;
        }
    }

    /// Resolves every binding, then every path, and gives the graph.
    fn finish(self) -> Result<Graph, String> {
        let n = self.bindings.len();
        let mut done: Vec<Option<Res>> = vec![None; n];
        let mut state: Vec<(usize, Res)> = self
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
                let step = self.advance(&self.bindings[x].segs, &mut pos, &mut at, &done);
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
        let mut found: HashMap<(usize, usize), Cite> = HashMap::new();
        let mut add = |from: usize, to: usize, line: usize, segs: &[&str]| {
            if from == to {
                return;
            }
            let earlier = found.get(&(from, to)).is_some_and(|c| c.line <= line);
            if !earlier {
                let path = segs.join("::");
                found.insert((from, to), Cite { line, path });
            }
        };
        for (x, binding) in self.bindings.iter().enumerate() {
            let from = self.modules[binding.module].file;
            match done[x] {
                Some(Res::Item(f)) => add(from, f, binding.line, &binding.segs),
                Some(Res::Module(m)) if binding.glob => {
                    add(from, self.modules[m].file, binding.line, &binding.segs);
                }
                _ => {}
            }
        }
        for path in &self.paths {
            let (mut pos, mut at) = (0, Res::Module(path.module));
            // Every binding is resolved by now, so the path resolves to its end.
            if let Step::Done(Res::Item(f)) = self.advance(&path.segs, &mut pos, &mut at, &done) {
                add(self.modules[path.module].file, f, path.line, &path.segs);
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
        for ((from, to), cite) in found {
            imports[number[from]].push((number[to], cite));
        }
        for list in &mut imports {
            list.sort_unstable_by_key(|&(g, _)| g);
        }
        Ok(Graph {
            undeclared: self.files.len() - files.len(),
            placed: self.placed,
            files,
            imports,
        })
    }
}

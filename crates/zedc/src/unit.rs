//! The units of a package (step L2.3, DESIGN.md sec:units): the manifest that marks the
//! package root, the file each unit path names, and the loader that reads a package's units
//! into the query database and resolves each one after the units it imports.
//!
//! A unit path `geometry.shapes` names the file `geometry/shapes.zed` under the root. The
//! loader reads the units the roots import, and the units those import, once each; orders them
//! by the strongly connected components of the import graph, found by a depth-first search
//! with a visited set, so that each unit is resolved after the units it imports, in time
//! linear in the units and imports; and rejects the imports inside each component, which all
//! lie on cycles, reporting each component once at an import the graph alone fixes, naming
//! every unit and import on one cycle through it (DESIGN.md sec:units). A unit is resolved by
//! the query [`Query::Resolve`](crate::query::Query::Resolve), keyed by its text and the
//! exports of the units it imports, so an edit that leaves a unit's exports alone resolves no
//! importer again. Linking a use of another unit's name to its definition is step L2.4.
//!
//! Nothing here depends on the order of the roots or on the order in which the loader meets
//! units: the components, the order of the units, the import each cycle is reported at, its
//! text, and the order of the problems (by file, each file's in a fixed order) are the same for
//! every order of the roots, and so for a unit checked alone and in a batch.
//!
//! Where DESIGN.md does not say: a unit on an import cycle sees none of the units of its
//! component, whose imports of each other are each rejected, with the names they bring in bound
//! but unchecked; a manifest that cannot be read or parsed stops the package before any unit is
//! read.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::ast::{self, Error, ExprKind, Note, StmtKind, StrPart, Target};
use crate::lex::{self, Span, Tok};
use crate::parse::{TOP, parse};
use crate::query::{self, Db, Parsed};
use crate::resolve::{self, Alone, Exports, Refused, Resolved, Units};
use crate::run::{self, Diagnostic};
use crate::source;
use crate::suppress::Severity;

/// The name of the manifest file, which marks the package root.
pub const MANIFEST: &str = "zed.manifest";

/// The files under a package root.
pub trait Files {
    /// The text of the file `name`, a path under the root with `/` between its parts: `None`
    /// when there is no such file, or why it cannot be read.
    fn read(&self, name: &str) -> Option<Result<Arc<str>, Unreadable>>;
}

/// Why a file cannot be read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unreadable {
    /// The line and column in the file where the rejection starts, when it has a place.
    pub at: Option<(usize, usize)>,
    /// Why, with no position.
    pub why: String,
}

/// The file `file` cannot be read, for `u`: `file:line:col: the file cannot be read: why`, or
/// ``the file `file` cannot be read: why`` when `u` has no place in it.
fn unreadable(file: &str, u: &Unreadable) -> String {
    match u.at {
        Some((line, col)) => format!("{file}:{line}:{col}: the file cannot be read: {}", u.why),
        None => format!("the file `{file}` cannot be read: {}", u.why),
    }
}

/// The files under a directory of the file system, each loaded as source (DESIGN.md
/// sec:lexical): one that is not UTF-8, starts with a byte order mark or is not NFC cannot be
/// read, at the line and column of the rejection.
pub struct Dir(pub PathBuf);

impl Files for Dir {
    fn read(&self, name: &str) -> Option<Result<Arc<str>, Unreadable>> {
        match std::fs::read(self.0.join(name)) {
            Ok(bytes) => Some(source::load(&bytes).map(Arc::from).map_err(|e| Unreadable {
                at: Some(source::line_col(&bytes, e.span().start)),
                why: e.message(&bytes),
            })),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
            Err(e) => Some(Err(Unreadable {
                at: None,
                why: e.to_string(),
            })),
        }
    }
}

/// Files held in memory, by name.
#[derive(Default)]
pub struct Memory(pub HashMap<String, Arc<str>>);

impl Files for Memory {
    fn read(&self, name: &str) -> Option<Result<Arc<str>, Unreadable>> {
        self.0.get(name).map(|t| Ok(t.clone()))
    }
}

/// What a manifest says.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Manifest {
    /// The path of the prelude unit and the text of its string, if the manifest names one.
    pub prelude: Option<(String, Span)>,
}

/// The start of a file, where an error about the whole file is placed.
const NOWHERE: Span = Span { start: 0, end: 0 };

/// An error at `span` with no derivation.
fn error(span: Span, message: String) -> Error {
    Error {
        row: None,
        span,
        message,
        notes: Vec::new(),
    }
}

/// The manifest `text`, or every error in it: it is written in unit syntax and binds only
/// names to string literals, each name once, and `prelude` is the one name it may bind.
pub fn manifest(text: &str) -> Result<Manifest, Vec<Error>> {
    let tokens = lex::lex(text).map_err(|e| vec![error(e.span, e.to_string())])?;
    let tree = parse(text, &tokens, "Unit", TOP).map_err(|e| vec![error(e.span, e.to_string())])?;
    let stmts = ast::unit_all_errors(text, &tokens, &tree)?;
    let mut out = Manifest::default();
    let mut errors = Vec::new();
    let mut seen: HashMap<&str, Span> = HashMap::new();
    for s in &stmts {
        let StmtKind::Bind {
            targets,
            value,
            boundary,
        } = &s.kind
        else {
            errors.push(error(
                s.span,
                "a manifest holds only bindings of string literals, as \
                 `prelude = \"std.prelude\";`"
                    .into(),
            ));
            continue;
        };
        let ([Target::Name(name, at)], true) = (&targets[..], boundary.is_empty()) else {
            errors.push(error(
                s.span,
                "a manifest entry binds one name to a string literal, as \
                 `prelude = \"std.prelude\";`"
                    .into(),
            ));
            continue;
        };
        let string = match &value.kind {
            ExprKind::Str(parts) => parts
                .iter()
                .map(|p| match p {
                    StrPart::Text(t) => Some(t.as_str()),
                    _ => None,
                })
                .collect::<Option<String>>(),
            _ => None,
        };
        let Some(string) = string else {
            errors.push(error(
                value.span,
                format!(
                    "the manifest entry `{name}` is bound to a string literal with no hole, \
                     as `{name} = \"std.prelude\";`"
                ),
            ));
            continue;
        };
        if let Some(&first) = seen.get(name.as_str()) {
            errors.push(Error {
                row: None,
                span: *at,
                message: format!("the manifest binds `{name}` twice"),
                notes: vec![Note {
                    span: first,
                    text: format!("`{name}` is first bound here"),
                }],
            });
            continue;
        }
        seen.insert(name, *at);
        if name != "prelude" {
            errors.push(error(
                *at,
                format!(
                    "the manifest has no entry `{name}`: its one entry is `prelude`, the path \
                     of the package's prelude unit"
                ),
            ));
            continue;
        }
        match bad_segment(&string) {
            Some(seg) => errors.push(error(
                value.span,
                format!("the prelude `{string}` is not a unit path: `{seg}` is not a name"),
            )),
            None => out.prelude = Some((string, value.span)),
        }
    }
    if errors.is_empty() {
        Ok(out)
    } else {
        Err(errors)
    }
}

/// The first part of the dotted path `path` that is not a `Name`, if any.
fn bad_segment(path: &str) -> Option<&str> {
    path.split('.').find(|seg| {
        !matches!(lex::lex(seg).as_deref(),
            Ok([t]) if matches!(t.tok, Tok::Name(_)) && t.span.end - t.span.start == seg.len())
    })
}

/// The file the unit path `path` names under the package root: `geometry.shapes` names
/// `geometry/shapes.zed`.
pub fn file_of(path: &str) -> String {
    format!("{}.zed", path.replace('.', "/"))
}

/// The unit path of the file `file`, a path under the package root with `/` between its
/// parts, or why it names no unit: each directory and the file's stem is a `Name`, and the
/// file ends in `.zed`.
pub fn unit_of(file: &str) -> Result<String, String> {
    let Some(stem) = file.strip_suffix(".zed") else {
        return Err(format!(
            "the file `{file}` is not a unit: its name does not end in `.zed`"
        ));
    };
    let path = stem.replace('/', ".");
    match bad_segment(&path) {
        Some(seg) => Err(format!(
            "the file `{file}` names no unit: `{seg}` is not a name, and each directory under \
             the package root and the file's stem must be one"
        )),
        None => Ok(path),
    }
}

/// The statements of the unit `text` and its imports, each with the unit it names, in text
/// order; or the errors of the first phase that rejects it. What [`Query::Parse`] computes.
///
/// [`Query::Parse`]: crate::query::Query::Parse
pub(crate) fn parse_unit(text: &str) -> Parsed {
    let tokens = lex::lex(text).map_err(|e| vec![error(e.span, e.to_string())])?;
    let tree = parse(text, &tokens, "Unit", TOP).map_err(|e| vec![error(e.span, e.to_string())])?;
    let stmts = ast::unit_all_errors(text, &tokens, &tree)?;
    // The imports are found by the resolver's own walk, which meets every import in every
    // scope; read alone, the unit resolves with no other unit, and only the imports are kept.
    let mut imports = resolve::resolve_in(&stmts, &Alone).res.units;
    imports.sort_by_key(|i| i.1);
    Ok((stmts, imports))
}

/// A unit the loader read.
#[derive(Debug)]
pub struct Loaded {
    /// Its path.
    pub path: Arc<str>,
    /// Its file under the root.
    pub file: String,
    /// Its text, or `None` when there is no such file, or why it cannot be read.
    pub text: Option<Result<Arc<str>, Unreadable>>,
    /// Its statements and imports, when its text parses.
    pub parsed: Option<Arc<Parsed>>,
    /// Its resolution, once it is resolved.
    pub resolved: Option<Arc<Resolved>>,
}

/// An error of a package, in the file it is about.
#[derive(Debug)]
pub struct Problem {
    /// The file, under the root.
    pub file: String,
    /// The error, placed in the file's text when the file has one.
    pub error: Error,
}

/// A package's units, in the order the loader found them, and its errors.
#[derive(Debug, Default)]
pub struct Package {
    /// The manifest's text, or why it cannot be read; `None` when there is none.
    pub manifest: Option<Result<Arc<str>, Unreadable>>,
    /// The units.
    pub units: Vec<Loaded>,
    /// Each unit's index in `units`, by path.
    pub index: HashMap<Arc<str>, usize>,
    /// The units in dependency order: each after the units it imports outside its strongly
    /// connected component, the units of a component together, in order of their paths. The
    /// order depends only on the import graph and the units' paths, never on the roots' order.
    pub order: Vec<usize>,
    /// The errors of the manifest, of a root that names no file, and of each unit: a
    /// rejection of each import of a unit with no file, or one that does not parse; each import
    /// cycle, once per strongly connected component and once per unit that imports itself; and
    /// each unit's own errors and forms of later steps. In order of their files, each file's in
    /// an order fixed by its text and the package.
    pub problems: Vec<Problem>,
}

impl Package {
    /// The unit `path`, if the loader read it.
    pub fn unit(&self, path: &str) -> Option<&Loaded> {
        self.index.get(path).map(|&i| &self.units[i])
    }

    /// Each problem as `zedc` prints it, as `file:line:col: message` and its derivation, the
    /// file written under `root`; a file that cannot be read gives `file:line:col: message` at
    /// the place it was rejected, or `file: message` when the reason has no place.
    pub fn report(&self, root: &Path) -> Vec<String> {
        let mut lines: HashMap<&str, (&str, source::Lines)> = HashMap::new();
        let mut out = Vec::with_capacity(self.problems.len());
        for p in &self.problems {
            let file = root.join(&p.file);
            let text = if p.file == MANIFEST {
                self.manifest.as_ref()
            } else {
                self.unit_of_file(&p.file).and_then(|u| u.text.as_ref())
            };
            let text = match text {
                Some(Ok(text)) => text,
                Some(Err(Unreadable {
                    at: Some((line, col)),
                    ..
                })) => {
                    out.push(format!(
                        "{}:{line}:{col}: {}",
                        file.display(),
                        p.error.message
                    ));
                    continue;
                }
                _ => {
                    out.push(format!("{}: {}", file.display(), p.error.message));
                    continue;
                }
            };
            let (text, l) = lines
                .entry(&p.file)
                .or_insert_with(|| (text, source::Lines::new(text.as_bytes())));
            let d: Vec<Diagnostic> =
                run::placed(text, l, &[], Severity::Rejection, vec![p.error.clone()]);
            for d in d {
                out.push(format!("{}:{d}", file.display()));
            }
        }
        out
    }

    /// The unit whose file is `file`.
    fn unit_of_file(&self, file: &str) -> Option<&Loaded> {
        unit_of(file).ok().and_then(|p| self.unit(&p))
    }
}

/// The index of the unit `path` in `pkg`, which is added and put on `todo` to be read when the
/// loader has not met it.
fn add(pkg: &mut Package, todo: &mut Vec<Arc<str>>, path: &Arc<str>) -> usize {
    if let Some(&i) = pkg.index.get(path) {
        return i;
    }
    let i = pkg.units.len();
    pkg.index.insert(path.clone(), i);
    pkg.units.push(Loaded {
        path: path.clone(),
        file: file_of(path),
        text: None,
        parsed: None,
        resolved: None,
    });
    todo.push(path.clone());
    i
}

/// The package under `files` that the units `roots` reach, each unit resolved through `db`
/// after the units it imports.
pub fn load(db: &mut Db, files: &dyn Files, roots: &[&str]) -> Package {
    let mut pkg = Package::default();
    let manifest = match files.read(MANIFEST) {
        None => Manifest::default(),
        Some(Err(u)) => {
            pkg.problems.push(Problem {
                file: MANIFEST.into(),
                error: error(NOWHERE, format!("the manifest cannot be read: {}", u.why)),
            });
            pkg.manifest = Some(Err(u));
            return pkg;
        }
        Some(Ok(text)) => {
            let m = manifest(&text);
            pkg.manifest = Some(Ok(text));
            match m {
                Ok(m) => m,
                Err(errors) => {
                    pkg.problems.extend(errors.into_iter().map(|error| Problem {
                        file: MANIFEST.into(),
                        error,
                    }));
                    return pkg;
                }
            }
        }
    };
    // Read every unit the roots and the prelude reach, once each: `index` is the visited set.
    let mut edges: Vec<Vec<(usize, Span)>> = Vec::new();
    let mut todo: Vec<Arc<str>> = Vec::new();
    let prelude = manifest
        .prelude
        .as_ref()
        .map(|(p, span)| (add(&mut pkg, &mut todo, &Arc::from(p.as_str())), *span));
    for r in roots {
        add(&mut pkg, &mut todo, &Arc::from(*r));
    }
    while let Some(path) = todo.pop() {
        let i = pkg.index[&path];
        if i >= edges.len() {
            edges.resize_with(i + 1, Vec::new);
        }
        let text = files.read(&pkg.units[i].file);
        if let Some(Ok(t)) = &text {
            let parsed = db.parse(t);
            match &*parsed {
                Ok((_, imports)) => {
                    for (unit, span) in imports {
                        let j = add(&mut pkg, &mut todo, unit);
                        edges[i].push((j, *span));
                    }
                }
                Err(errors) => pkg.problems.extend(errors.iter().map(|e| Problem {
                    file: pkg.units[i].file.clone(),
                    error: e.clone(),
                })),
            }
            pkg.units[i].parsed = Some(parsed);
        }
        pkg.units[i].text = text;
    }
    edges.resize_with(pkg.units.len(), Vec::new);
    for &r in roots {
        let u = &pkg.units[pkg.index[r]];
        match &u.text {
            None => pkg.problems.push(Problem {
                file: u.file.clone(),
                error: error(
                    NOWHERE,
                    format!(
                        "there is no unit `{r}`: no file `{}` under the root",
                        u.file
                    ),
                ),
            }),
            Some(Err(why)) => pkg.problems.push(Problem {
                file: u.file.clone(),
                error: error(NOWHERE, format!("the file cannot be read: {}", why.why)),
            }),
            Some(Ok(_)) => {}
        }
    }
    if let Some((p, span)) = prelude
        && pkg.units[p].parsed.is_none()
    {
        let u = &pkg.units[p];
        let why = match &u.text {
            None => format!("there is no file `{}` under the root", u.file),
            Some(Err(why)) => unreadable(&u.file, why),
            Some(Ok(_)) => unreachable!("a unit with text is parsed"),
        };
        pkg.problems.push(Problem {
            file: MANIFEST.into(),
            error: error(
                span,
                format!("the prelude unit `{}` is missing: {why}", u.path),
            ),
        });
    }
    let comp = order(&mut pkg, &edges, prelude.map(|(p, _)| p));
    // The prelude unit and every unit it reaches see no prelude unit.
    let mut bare = vec![false; pkg.units.len()];
    if let Some((p, _)) = prelude {
        let mut stack = vec![p];
        bare[p] = true;
        while let Some(u) = stack.pop() {
            for &(v, _) in &edges[u] {
                if !bare[v] {
                    bare[v] = true;
                    stack.push(v);
                }
            }
        }
    }
    // The number the database gives each resolved unit's exports, for its importers' keys: a
    // key holds what it reads, never a hash of it (step L1.37a), and a number per unit keeps
    // an importer's key the size of its imports.
    let mut numbers = vec![[0u8; 8]; pkg.units.len()];
    for k in 0..pkg.order.len() {
        let u = pkg.order[k];
        let Some(parsed) = pkg.units[u].parsed.clone() else {
            continue;
        };
        let Ok((stmts, _)) = &*parsed else {
            continue;
        };
        let mut deps: Vec<Dep> = Vec::new();
        let mut named = HashSet::new();
        for &(v, _) in &edges[u] {
            if !named.insert(v) {
                continue;
            }
            let dep = &pkg.units[v];
            let because = |why: String| Err(Refused::Because(why));
            // An import inside the unit's component lies on a cycle, which `order` reported.
            let got = match (&dep.resolved, &dep.text, &dep.parsed) {
                _ if comp[v] == comp[u] => Err(Refused::OnCycle),
                (Some(r), _, _) => Ok(r.clone()),
                (None, None, _) => {
                    because(format!("there is no file `{}` under the root", dep.file))
                }
                (None, Some(Err(why)), _) => because(unreadable(&dep.file, why)),
                (None, Some(Ok(_)), Some(p)) if p.is_err() => because(format!(
                    "the file `{}` does not parse, so the names it defines are not known",
                    dep.file
                )),
                (None, _, _) => {
                    unreachable!("a unit's imports outside its component are put before it")
                }
            };
            deps.push((dep.path.clone(), got));
        }
        deps.sort_by(|a, b| a.0.cmp(&b.0));
        let prelude = prelude
            .filter(|_| !bare[u])
            .and_then(|(p, _)| Some((pkg.units[p].path.clone(), pkg.units[p].resolved.clone()?)));
        let Some(Ok(text)) = &pkg.units[u].text else {
            unreachable!("a parsed unit has text")
        };
        let mut parts: Vec<&[u8]> = vec![text.as_bytes()];
        for (path, d) in &deps {
            let read = match d {
                Ok(_) => Read::Unit(&numbers[pkg.index[path]]),
                Err(Refused::Because(why)) => Read::Failed(why),
                Err(Refused::OnCycle) => Read::OnCycle,
            };
            push_read(&mut parts, path, read);
        }
        if let Some((path, _)) = &prelude {
            push_read(&mut parts, path, Read::Prelude(&numbers[pkg.index[path]]));
        }
        let k = query::key("resolve", &parts);
        let linked = Linked { deps, prelude };
        let r = db.resolve(k, || resolve::resolve_in(stmts, &linked));
        let file = &pkg.units[u].file;
        for e in r.errors.iter().chain(&r.later) {
            pkg.problems.push(Problem {
                file: file.clone(),
                error: e.clone(),
            });
        }
        numbers[u] = db.exports_number(&r.res.exports).to_le_bytes();
        pkg.units[u].resolved = Some(r);
    }
    // The problems were met in an order that follows the roots (the units read, those that do
    // not parse, the roots with no file); by file, each file's in the order it was given them,
    // they are the same for every order of the roots. A stable sort, O(P log P).
    pkg.problems.sort_by(|a, b| a.file.cmp(&b.file));
    pkg
}

/// Puts the units of `pkg` in `pkg.order` by the strongly connected components of the import
/// graph `edges`, and reports each import cycle in `pkg.problems`; returns each unit's
/// component, the components numbered in the order they are put.
///
/// The components are found by Tarjan's algorithm on an explicit stack, each unit and import
/// met once. The search starts from the units in order of their paths and takes each unit's
/// imports in the order of its text, so the order of the components, each after the
/// components it imports, depends on the graph and the paths alone, never on the order of the
/// roots or of the indices the loader gave the units; a component's units are put in order of
/// their paths. The search starts first from the `prelude` unit, so it and the units it reaches
/// come before every unit that sees it, as each such unit's resolution reads it. Each import
/// inside a component lies on a cycle, since the unit it names reaches back. A unit that
/// imports itself is reported at its first import of itself, and a component of two units or
/// more once, by [`report`]. Time O(U log U + E + T) for U units, E imports and T the bytes of
/// the units whose imports a report names: the sort by path, one visit of each unit and import,
/// and the lines of those units. Public for the scaling tests, which time it on import graphs
/// built with no file read: reading, parsing and resolving a unit costs far more than ordering
/// it, and would hide a cost per pair of units here.
#[doc(hidden)]
pub fn order(
    pkg: &mut Package,
    edges: &[Vec<(usize, Span)>],
    prelude: Option<usize>,
) -> Vec<usize> {
    const UNSEEN: usize = usize::MAX;
    let n = pkg.units.len();
    let mut starts: Vec<usize> = (0..n).collect();
    starts.sort_unstable_by(|&a, &b| pkg.units[a].path.cmp(&pkg.units[b].path));
    starts.splice(0..0, prelude);
    // When each unit was met, and the earliest-met unit still on `stack` that it reaches.
    let (mut met, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut comp = vec![UNSEEN; n];
    // The units met whose component is not yet found, and where each stands on it.
    let (mut stack, mut at): (Vec<usize>, Vec<usize>) = (Vec::new(), vec![0; n]);
    // The search's path: each unit on it and how many of its imports are taken.
    let mut path: Vec<(usize, usize)> = Vec::new();
    let mut search = Search {
        queue: Vec::new(),
        met: vec![UNSEEN; n],
        by: vec![(0, NOWHERE); n],
        lines: (0..n).map(|_| None).collect(),
    };
    let (mut count, mut comps) = (0, 0);
    for &s in &starts {
        if met[s] != UNSEEN {
            continue;
        }
        (met[s], low[s], at[s]) = (count, count, stack.len());
        count += 1;
        stack.push(s);
        path.push((s, 0));
        while let Some(&(u, e)) = path.last() {
            if let Some(&(v, _)) = edges[u].get(e) {
                path.last_mut().expect("the unit read").1 = e + 1;
                if met[v] == UNSEEN {
                    (met[v], low[v], at[v]) = (count, count, stack.len());
                    count += 1;
                    stack.push(v);
                    path.push((v, 0));
                } else if comp[v] == UNSEEN {
                    low[u] = low[u].min(met[v]);
                }
                continue;
            }
            path.pop();
            if let Some(&(p, _)) = path.last() {
                low[p] = low[p].min(low[u]);
            }
            if low[u] == met[u] {
                let members = &mut stack[at[u]..];
                members.sort_unstable_by(|&a, &b| pkg.units[a].path.cmp(&pkg.units[b].path));
                for &x in members.iter() {
                    comp[x] = comps;
                }
                pkg.order.extend_from_slice(members);
                report(
                    &pkg.units,
                    &mut pkg.problems,
                    edges,
                    (&comp, comps),
                    members,
                    &mut search,
                );
                stack.truncate(at[u]);
                comps += 1;
            }
        }
    }
    comp
}

/// The breadth-first search that finds the cycle a component is reported with, kept across
/// components so that each search costs only its own component: the units waiting, the
/// component whose search met each unit, and the unit and import each was met by; and the
/// lines of each unit whose imports a report names.
struct Search {
    queue: Vec<usize>,
    met: Vec<usize>,
    by: Vec<(usize, Span)>,
    lines: Vec<Option<source::Lines>>,
}

/// Reports the import cycles of the component `c` (of the numbering `comp`), whose units are
/// `members` in order of their paths: each self-import, at the unit's first import of itself;
/// and, for a component of two units or more, the shortest cycle through its first unit `c0`
/// that leaves no unit for itself, of those the one whose imports come first in their units'
/// texts, at the import of `c0` that begins it, written from `c0`. A breadth-first search from
/// `c0` within the component, taking each unit's imports in text order, finds it, since it
/// meets each unit first by a shortest path and, of those, the one whose imports come first;
/// the first import back to `c0` it takes closes the cycle. O(units + imports) of the
/// component, and the lines of the units on the cycle.
fn report(
    units: &[Loaded],
    problems: &mut Vec<Problem>,
    edges: &[Vec<(usize, Span)>],
    (comp, c): (&[usize], usize),
    members: &[usize],
    search: &mut Search,
) {
    for &u in members {
        if let Some(&(_, span)) = edges[u].iter().find(|&&(v, _)| v == u) {
            problems.push(cycle_error(units, &mut search.lines, &[(u, span, u)]));
        }
    }
    let [c0, _, ..] = *members else {
        return;
    };
    search.queue.clear();
    search.queue.push(c0);
    search.met[c0] = c;
    let mut head = 0;
    let (last, close) = 'search: loop {
        let u = *search
            .queue
            .get(head)
            .expect("a component of two units has a cycle through each of them");
        head += 1;
        for &(v, span) in &edges[u] {
            if comp[v] != c || v == u {
                continue;
            }
            if v == c0 {
                break 'search (u, span);
            }
            if search.met[v] != c {
                search.met[v] = c;
                search.by[v] = (u, span);
                search.queue.push(v);
            }
        }
    };
    let mut steps = vec![(last, close, c0)];
    let mut x = last;
    while x != c0 {
        let (from, span) = search.by[x];
        steps.push((from, span, x));
        x = from;
    }
    steps.reverse();
    problems.push(cycle_error(units, &mut search.lines, &steps));
}

/// The rejection of the import cycle `steps`, each a unit, its import and the unit it names, in
/// order: at the first step's import, naming each step with its file, line and column.
fn cycle_error(
    units: &[Loaded],
    lines: &mut [Option<source::Lines>],
    steps: &[(usize, Span, usize)],
) -> Problem {
    let named: Vec<String> = steps
        .iter()
        .map(|&(from, span, to)| {
            let unit = &units[from];
            let Some(Ok(text)) = &unit.text else {
                unreachable!("a unit with imports has text")
            };
            let l = lines[from].get_or_insert_with(|| source::Lines::new(text.as_bytes()));
            let (line, col) = l.line_col(text.as_bytes(), span.start);
            format!(
                "`{}` imports `{}` at {}:{line}:{col}",
                unit.path, units[to].path, unit.file
            )
        })
        .collect();
    let (from, span, to) = steps[0];
    Problem {
        file: units[from].file.clone(),
        error: error(
            span,
            format!(
                "the unit `{}` cannot be imported: the imports form a cycle, so its units have no \
                 order to be resolved in: {}",
                units[to].path,
                named.join(", ")
            ),
        ),
    }
}

/// What a unit's resolution reads of another unit: an import resolved to the number of its
/// exports, an import that failed and why, the prelude unit with the number of its exports, or
/// an import on a cycle, which fails with no error of its own.
enum Read<'a> {
    Unit(&'a [u8; 8]),
    Failed(&'a str),
    Prelude(&'a [u8; 8]),
    OnCycle,
}

/// Appends to the parts of a resolve key what the resolution reads of the unit `path`: its
/// path, a tag byte that says which kind of [`Read`] follows, and the read itself. The tag
/// keeps apart a failed import whose text has the bytes of an exports number from a resolved
/// one, and the prelude from an import of the same unit.
fn push_read<'a>(parts: &mut Vec<&'a [u8]>, path: &'a str, read: Read<'a>) {
    parts.push(path.as_bytes());
    match read {
        Read::Unit(n) => parts.extend([&[0][..], n]),
        Read::Failed(why) => parts.extend([&[1][..], why.as_bytes()]),
        Read::Prelude(n) => parts.extend([&[2][..], n]),
        Read::OnCycle => parts.push(&[3]),
    }
}

/// A unit a unit imports, by path, resolved or with why it is not.
type Dep = (Arc<str>, Result<Arc<Resolved>, Refused>);

/// The units a unit imports, each resolved or with why it is not, and the prelude unit it
/// sees: what its resolution reads.
struct Linked {
    deps: Vec<Dep>,
    prelude: Option<(Arc<str>, Arc<Resolved>)>,
}

impl Units for Linked {
    fn exports(&self, path: &str) -> Result<&Exports, Refused> {
        let i = self
            .deps
            .binary_search_by(|d| (*d.0).cmp(path))
            .expect("the loader gives each unit every unit its imports name");
        match &self.deps[i].1 {
            Ok(r) => Ok(&r.res.exports),
            Err(why) => Err(why.clone()),
        }
    }

    fn prelude(&self) -> Option<(&Arc<str>, &Exports)> {
        self.prelude.as_ref().map(|(p, r)| (p, &r.res.exports))
    }
}

/// The package root of the file `file`: the nearest directory at or above it that holds a
/// manifest, and the file's path under it with `/` between its parts; `None` when no directory
/// above holds one.
pub fn root_of(file: &Path) -> Result<Option<(PathBuf, String)>, String> {
    let full = std::fs::canonicalize(file).map_err(|e| format!("{}: {e}", file.display()))?;
    let mut dir = full.parent();
    while let Some(d) = dir {
        if d.join(MANIFEST).is_file() {
            let rel = full.strip_prefix(d).expect("the root is above the file");
            let rel: Vec<&str> = rel
                .components()
                .map(|c| c.as_os_str().to_str())
                .collect::<Option<_>>()
                .ok_or_else(|| format!("{}: the path is not UTF-8", file.display()))?;
            return Ok(Some((d.to_path_buf(), rel.join("/"))));
        }
        dir = d.parent();
    }
    Ok(None)
}

/// What `zedc run` reports of the package of the unit `file`, read as `text`: `None` when the
/// unit compiles alone, since it has no manifest above it, or it imports nothing and its
/// manifest names no prelude unit; otherwise each problem of the package its unit reaches,
/// the files written under the root as `file`'s directory names it.
pub fn package_report(file: &Path, text: &str) -> Result<Option<Vec<String>>, String> {
    let Some((root, rel)) = root_of(file)? else {
        return Ok(None);
    };
    let mut db = Db::new();
    let imports = matches!(&*db.parse(text), Ok((_, i)) if !i.is_empty());
    let dir = Dir(root.clone());
    let prelude = match dir.read(MANIFEST) {
        Some(Ok(m)) => !matches!(manifest(&m), Ok(Manifest { prelude: None })),
        _ => true,
    };
    if !imports && !prelude {
        return Ok(None);
    }
    let path = unit_of(&rel)?;
    let pkg = load(&mut db, &dir, &[&path]);
    // The root as the command line reached it: the file's directory, and up from there.
    let depth = path.matches('.').count();
    let shown = file.parent().and_then(|p| p.ancestors().nth(depth));
    Ok(Some(pkg.report(shown.unwrap_or(&root))))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{Read, push_read};
    use crate::query::{Key, key};

    /// The resolve key of a unit whose text is `text` and that reads `read` of the unit `a`.
    fn resolve_key(text: &str, read: Read) -> Key {
        let mut parts: Vec<&[u8]> = vec![text.as_bytes()];
        push_read(&mut parts, "a", read);
        key("resolve", &parts)
    }

    #[test]
    fn a_failed_import_never_shares_a_key_with_a_resolved_one() {
        // A failure whose text is the eight bytes of an exports number: told apart only by
        // the tag, since the lengths are equal.
        let number = 0x6f_6f_6f_6f_6f_6f_6f_6f_u64.to_le_bytes();
        let why = std::str::from_utf8(&number).unwrap();
        let unit = resolve_key("import a;", Read::Unit(&number));
        assert_ne!(unit, resolve_key("import a;", Read::Failed(why)));
        assert_ne!(unit, resolve_key("import a;", Read::Prelude(&number)));
        assert_eq!(unit, resolve_key("import a;", Read::Unit(&number)));
    }

    /// Eight bytes, each the tag of an import on a cycle.
    const THREES: [u8; 8] = [3; 8];

    /// The `i`-th of 18 reads: of the unit `a`, or of one whose path is the tag byte 1 or 3, each
    /// a resolved unit, a failure whose text is empty or one of those tag bytes, the prelude, or
    /// an import on a cycle.
    fn nth_read(i: usize) -> (&'static str, Read<'static>) {
        let path = ["a", "\u{1}", "\u{3}"][i / 6];
        let read = match i % 6 {
            0 => Read::Unit(&THREES),
            1 => Read::Failed(""),
            2 => Read::Failed("\u{1}"),
            3 => Read::Failed("\u{3}"),
            4 => Read::Prelude(&THREES),
            _ => Read::OnCycle,
        };
        (path, read)
    }

    #[test]
    fn no_two_lists_of_reads_share_a_resolve_key() {
        // Every list of up to three of the reads: an import on a cycle, the tag 3 with nothing
        // after it, never shares a key with a failure whose text is empty or tag bytes, nor
        // with a read of a unit whose path is a tag after it.
        let mut lists: Vec<Vec<usize>> = vec![Vec::new()];
        let mut from = 0;
        for _ in 0..3 {
            let to = lists.len();
            for l in from..to {
                for i in 0..18 {
                    let mut next = lists[l].clone();
                    next.push(i);
                    lists.push(next);
                }
            }
            from = to;
        }
        let mut seen: HashMap<Key, usize> = HashMap::new();
        for (n, l) in lists.iter().enumerate() {
            let mut parts: Vec<&[u8]> = vec![b"import a;"];
            for &i in l {
                let (path, read) = nth_read(i);
                push_read(&mut parts, path, read);
            }
            if let Some(m) = seen.insert(key("resolve", &parts), n) {
                panic!("the reads {:?} and {l:?} share a key", lists[m]);
            }
        }
        assert_eq!(seen.len(), 1 + 18 + 18 * 18 + 18 * 18 * 18);
    }
}

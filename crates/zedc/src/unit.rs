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
use crate::front::{self, Diagnostic, Parsed, error};
use crate::lex::{self, Span, Tok};
use crate::parse::{TOP, parse};
use crate::pin::{self, Check, Edit, PIN_FILE, PRELUDE, Pins};
use crate::place::{MANIFEST, Place};
use crate::query::{self, Db};
use crate::resolve::{self, Exports, Refused, Resolved, Units};
use crate::source;
use crate::suppress::{InFile, Severity, Suppress, addresses};

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

impl Unreadable {
    /// The whole message, with no position: a rejection of the text explains itself, and a
    /// file the system would not give zedc says so, with the repair.
    pub fn sentence(&self) -> String {
        match self.at {
            Some(_) => self.why.clone(),
            None => format!(
                "zedc could not read this file: {}. Check the path and that you may read the file.",
                self.why
            ),
        }
    }
}

/// The file `file` cannot be read, for `u`: `file:line:col: why`, or `file: ` and
/// [`Unreadable::sentence`] when `u` has no place in it.
fn unreadable(file: &str, u: &Unreadable) -> String {
    match u.at {
        Some((line, col)) => format!("{file}:{line}:{col}: {}", u.why),
        None => format!("{file}: {}", u.sentence()),
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
                why: source::io_reason(&e),
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

/// The manifest `text`, or every error in it: it is written in unit syntax and binds only
/// names to string literals, each name once, and `prelude` is the one name it may bind.
pub fn manifest(text: &str) -> Result<Manifest, Vec<Error>> {
    let tokens = lex::lex(text).map_err(|e| vec![e.into()])?;
    let tree = parse(text, &tokens, "Unit", TOP).map_err(|e| vec![e.into()])?;
    let stmts = ast::unit_all_errors(text, &tokens, &tree)?;
    let mut out = Manifest::default();
    let mut errors = Vec::new();
    let mut seen: HashMap<&str, Span> = HashMap::new();
    for s in &stmts {
        let StmtKind::Bind { targets, value } = &s.kind else {
            errors.push(error(
                s.span,
                "a manifest holds only bindings of string literals, as \
                 `prelude = \"std.prelude\";`"
                    .into(),
            ));
            continue;
        };
        let [Target::Name(name, at)] = &targets[..] else {
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
                menu: String::new(),
                span: *at,
                message: format!(
                    "the manifest binds `{name}` twice, and a manifest binds each name once. \
                     Remove one of the two."
                ),
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

/// A problem of a package as `zedc` prints it.
struct Reported {
    /// Its place: `file:line:col`, or `file` when it has none in its file.
    place: String,
    /// Its place, its message and its derivation.
    text: String,
    /// The part of its address that its file's text decides ([`Diagnostic::address`]).
    part: crate::address::ContentAddress,
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
    /// The pin file's text ([`PIN_FILE`]), or why it cannot be read; `None` when there is none.
    pub pins: Option<Result<Arc<str>, Unreadable>>,
    /// The pins the build writes ([`Package::write_pins`]).
    pub writes: Writes,
}

/// The pins a build writes: those of the imports that have none, into their units' files, and
/// the pin file, when its pins change (step L2.8).
#[derive(Debug, Default)]
pub struct Writes {
    /// Each unit that gains a pin, by its index in [`Package::units`], with the text of each of
    /// its import statements that gains one and the edit that writes it, in text order.
    pub units: Vec<(usize, Vec<(Span, Edit)>)>,
    /// The pin file's new text, when its pins change.
    pub pin_file: Option<String>,
}

impl Package {
    /// The unit `path`, if the loader read it.
    pub fn unit(&self, path: &str) -> Option<&Loaded> {
        self.index.get(path).map(|&i| &self.units[i])
    }

    /// Each problem as `zedc` prints it, but for its address, as `file:line:col: message` and
    /// its derivation, the file written under `root`; a file that cannot be read gives
    /// `file:line:col: message` at the place it was rejected, or `file: message` when the
    /// reason has no place. It is for a package held in memory, whose files have no path for
    /// an address to name; [`Package::report_on_disk`] adds the addresses.
    pub fn report(&self, root: &Path) -> Vec<String> {
        self.reported(root).into_iter().map(|r| r.text).collect()
    }

    /// Each problem as `zedc` prints it, the package's files lying under `root`, the path the
    /// command line reached the root by: as [`Package::report`], each followed, under `--addresses`, by its
    /// address on a line of its own, `  address: <hex>`, as every diagnostic prints it, its file's part
    /// found from the file's path under the package root ([`InFile::named`]), never from
    /// `root`; then a line for each problem whose address `suppress` names, since a rejection
    /// cannot be suppressed. After [`Package::report`], O(t) for problems whose files' names
    /// total t bytes, each name counted once per problem: a hash of it, one BLAKE3 hash and one
    /// lookup in the suppressed set per problem.
    pub fn report_on_disk(&self, root: &Path, suppress: &mut Suppress) -> Vec<String> {
        let mut out = Vec::with_capacity(self.problems.len());
        let mut refused = Vec::new();
        for (p, r) in self.problems.iter().zip(self.reported(root)) {
            let address = InFile::named(&p.file).join(r.part);
            out.push(format!("{}{}", r.text, suppress.address_line(address)));
            refused.extend(suppress.refused_at(&r.place, address));
        }
        out.extend(refused);
        out
    }

    /// Each problem as [`Package::report`] prints it, with its place and the part of its
    /// address that its file's text decides: the address of a placed problem names the
    /// top-level declaration of its unit it lies in, as every rejection's does.
    fn reported(&self, root: &Path) -> Vec<Reported> {
        // The problems of each file are placed together, in one pass over its text, if it has
        // one (the addresses read the whole of it), and then written in the problems' order.
        type Group<'a> = (Option<&'a Result<Arc<str>, Unreadable>>, Vec<usize>);
        let mut groups: HashMap<&str, Group> = HashMap::new();
        for (i, p) in self.problems.iter().enumerate() {
            let text = if p.file == MANIFEST {
                self.manifest.as_ref()
            } else if p.file == PIN_FILE {
                self.pins.as_ref()
            } else {
                self.unit_of_file(&p.file).and_then(|u| u.text.as_ref())
            };
            groups
                .entry(&p.file)
                .or_insert_with(|| (text, Vec::new()))
                .1
                .push(i);
        }
        let mut out: Vec<Option<Reported>> = (0..self.problems.len()).map(|_| None).collect();
        for (name, (read, at)) in groups {
            let file = root.join(name);
            let file = file.display();
            let errors: Vec<Error> = at.iter().map(|&i| self.problems[i].error.clone()).collect();
            let text = match read {
                Some(Ok(text)) => text,
                // A file with no text: the address rests on the message alone, and the place
                // is where the file was rejected, if that has one.
                _ => {
                    let place = match read {
                        Some(Err(Unreadable {
                            at: Some((line, col)),
                            ..
                        })) => format!("{file}:{line}:{col}"),
                        _ => file.to_string(),
                    };
                    let parts = addresses("", &[], Severity::Rejection, &errors);
                    for ((i, e), part) in at.into_iter().zip(errors).zip(parts) {
                        out[i] = Some(Reported {
                            text: format!("{place}: {}", e.message),
                            place: place.clone(),
                            part,
                        });
                    }
                    continue;
                }
            };
            let stmts = match self.unit_of_file(name).and_then(|u| u.parsed.as_deref()) {
                Some(Ok((stmts, _))) if name != MANIFEST => &stmts[..],
                _ => &[],
            };
            let lines = source::Lines::new(text.as_bytes());
            let d: Vec<Diagnostic> =
                front::placed(text, &lines, stmts, Severity::Rejection, errors);
            for (i, d) in at.into_iter().zip(d) {
                out[i] = Some(Reported {
                    place: format!("{file}:{}:{}", d.line, d.col),
                    text: format!("{file}:{d}"),
                    part: d.address,
                });
            }
        }
        out.into_iter()
            .map(|r| r.expect("each problem is in its file's group"))
            .collect()
    }

    /// The unit whose file is `file`.
    fn unit_of_file(&self, file: &str) -> Option<&Loaded> {
        unit_of(file).ok().and_then(|p| self.unit(&p))
    }

    /// The text of the unit `path` with the pins the build writes into it, if it writes any.
    pub fn pinned(&self, path: &str) -> Option<String> {
        let &u = self.index.get(path)?;
        let (_, edits) = self.writes.units.iter().find(|(v, _)| *v == u)?;
        let Some(Ok(text)) = &self.units[u].text else {
            unreachable!("a unit that gains a pin has text")
        };
        Some(pin::apply(text, edits.iter().map(|(_, e)| e)))
    }

    /// Writes the pins the build writes ([`Package::writes`]) into the package's files, which
    /// lie under `root` and are shown under `shown`, the root as the command line reached it:
    /// each unit file's own bytes kept around its pins, and the pin file as the toolchain writes
    /// it. Each file that could not be written, as `file: why` and the repair. O(b + k log k)
    /// for files of b bytes in all and k pins.
    pub fn write_pins(&self, root: &Path, shown: &Path) -> Vec<String> {
        let mut failed = Vec::new();
        for (u, edits) in &self.writes.units {
            let unit = &self.units[*u];
            let Some(Ok(text)) = &unit.text else {
                unreachable!("a unit that gains a pin has text")
            };
            if let Err(why) =
                pin::write_edits(&root.join(&unit.file), text, edits.iter().map(|(_, e)| e))
            {
                let pinned: Vec<String> = edits
                    .iter()
                    .map(|(span, e)| {
                        let stmt = &text[span.start..span.end];
                        let at = e.at - span.start;
                        format!("`{}{}{}`", &stmt[..at], e.text, &stmt[at..])
                    })
                    .collect();
                failed.push(format!(
                    "{}: zedc could not write the pins of this file's imports: {why}. Each import \
                     is pinned to the content address of the unit it names, so that the next \
                     build checks it. Repairs: make the file writable and build again, or write \
                     the pins yourself: {}.",
                    shown.join(&unit.file).display(),
                    pinned.join(", ")
                ));
            }
        }
        if let Some(text) = &self.writes.pin_file {
            // A pin file that cannot be read gives the build no new pins to write.
            let read = match &self.pins {
                Some(Ok(read)) => Some(&**read),
                _ => None,
            };
            if let Err(why) = pin::write_file(&root.join(PIN_FILE), read, text) {
                failed.push(format!(
                    "{}: zedc could not write the pin file: {why}. It holds the content address \
                     of the package's prelude unit, which each build checks. Repair: make the \
                     package's directory and this file writable, and build again.",
                    shown.join(PIN_FILE).display()
                ));
            }
        }
        failed
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
                error: error(NOWHERE, u.sentence()),
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
    pkg.pins = files.read(PIN_FILE);
    if let Some(Err(u)) = &pkg.pins {
        pkg.problems.push(Problem {
            file: PIN_FILE.into(),
            error: error(NOWHERE, u.sentence()),
        });
    }
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
                    for (unit, span, _) in imports {
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
                error: error(NOWHERE, why.sentence()),
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
        let r = db.resolve(k, || resolve::resolve_in_text(stmts, &linked, Some(text)));
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
    pin_units(db, &mut pkg, prelude);
    // The problems were met in an order that follows the roots (the units read, those that do
    // not parse, the roots with no file); by file, each file's in the order it was given them,
    // they are the same for every order of the roots. A stable sort, O(P log P).
    pkg.problems.sort_by(|a, b| a.file.cmp(&b.file));
    pkg
}

/// Checks and writes the pins of `pkg` (step L2.8): each import is checked against, or pinned
/// to, the address of the unit it names, and the `prelude` unit, with the text of the manifest's
/// string that names it, against its pin in the pin file. A stale pin is a problem at the import,
/// or at the manifest's string; the pins to write go in [`Package::writes`]. Each unit is
/// addressed at most once, and only when an import or the manifest names it: O(t log t) for the
/// definitions of those units, of size t in all, the canonicalizer's cost, then O(s) for
/// import statements of s bytes and O(p log p) for p pins in the pin file.
fn pin_units(db: &mut Db, pkg: &mut Package, prelude: Option<(usize, Span)>) {
    let mut memo: Vec<Option<Arc<pin::Address>>> = vec![None; pkg.units.len()];
    for k in 0..pkg.order.len() {
        let u = pkg.order[k];
        let Some(parsed) = pkg.units[u].parsed.clone() else {
            continue;
        };
        let Ok((_, imports)) = &*parsed else {
            continue;
        };
        let Some(Ok(text)) = pkg.units[u].text.clone() else {
            unreachable!("a parsed unit has text")
        };
        let mut edits = Vec::new();
        for (path, span, pinned) in imports {
            let v = pkg.index[path];
            let address = unit_address(db, pkg, &mut memo, v);
            let now = match &*address {
                None => continue,
                Some(Err(too)) => {
                    let error = too_large(*span, &pkg.units[v].path, too);
                    pkg.problems.push(Problem {
                        file: pkg.units[u].file.clone(),
                        error,
                    });
                    continue;
                }
                Some(Ok(now)) => now.unit,
            };
            match pin::check(*pinned, now) {
                Check::Fresh => {}
                Check::Unpinned => {
                    edits.extend(pin::pin_import(&text, *span, now).map(|e| (*span, e)));
                }
                Check::Stale(old) => {
                    let dep = &pkg.units[v];
                    let repinned = pin::unpinned(&text, *span).unwrap_or_default();
                    let error = error(
                        *span,
                        format!(
                            "the import of the unit `{}` is pinned to the content address {old}, \
                             and the unit now has the address {now}: its exports, or a \
                             declaration they use, changed in `{}` after the pin was written. A \
                             pinned import is checked and never resolved again, so the build \
                             stops here. Repairs: to build with the unit as it is now, remove \
                             the pin, as `{repinned}`, and the next build writes the new \
                             address; or, to build with the unit as it was pinned, restore \
                             `{}` to that version.",
                            dep.path, dep.file, dep.file
                        ),
                    );
                    pkg.problems.push(Problem {
                        file: pkg.units[u].file.clone(),
                        error,
                    });
                }
            }
        }
        if !edits.is_empty() {
            pkg.writes.units.push((u, edits));
        }
    }
    // The pin file: a file that cannot be read, or holds a line that is no pin, is reported and
    // left as it is, and its pins are not checked.
    let mut pins = match &pkg.pins {
        None => Pins::default(),
        Some(Err(_)) => return,
        Some(Ok(text)) => match Pins::parse(text) {
            Ok(pins) => pins,
            Err(errors) => {
                pkg.problems.extend(errors.into_iter().map(|error| Problem {
                    file: PIN_FILE.into(),
                    error,
                }));
                return;
            }
        },
    };
    let mut changed = false;
    match prelude {
        // With no prelude unit, a pin of one is stale and goes.
        None => changed |= pins.drop_kind(PRELUDE, None),
        Some((p, span)) => {
            let path = pkg.units[p].path.clone();
            changed |= pins.drop_kind(PRELUDE, Some(&path));
            let address = unit_address(db, pkg, &mut memo, p);
            match &*address {
                None => {}
                Some(Err(too)) => pkg.problems.push(Problem {
                    file: MANIFEST.into(),
                    error: too_large(span, &path, too),
                }),
                Some(Ok(now)) => match pin::check(pins.get(PRELUDE, &path), now.unit) {
                    Check::Fresh => {}
                    Check::Unpinned => changed |= pins.set(PRELUDE, &path, now.unit, true),
                    Check::Stale(old) => {
                        let file = &pkg.units[p].file;
                        let error = error(
                            span,
                            format!(
                                "the prelude unit `{path}` is pinned in the pin file \
                                 `{PIN_FILE}` to the content address {old}, and it now has the \
                                 address {}: its exports, or a declaration they use, changed in \
                                 `{file}` after the pin was written. A pinned unit is checked \
                                 and never read afresh, so the build stops here. Repairs: to \
                                 build with the prelude as it is now, delete the line \
                                 `{PRELUDE} {old} {path}` from `{PIN_FILE}`, and the next build \
                                 writes the new address; or, to build with the prelude as it \
                                 was pinned, restore `{file}` to that version.",
                                now.unit
                            ),
                        );
                        pkg.problems.push(Problem {
                            file: MANIFEST.into(),
                            error,
                        });
                    }
                },
            }
        }
    }
    if changed {
        pkg.writes.pin_file = Some(pins.text());
    }
}

/// The address of the unit `v` of `pkg`, kept in `memo` once found: `None` when it has no text,
/// is not resolved, or does not compile alone.
///
/// Complexity tradeoff: naive version, a unit addressed again at each import that names it,
/// O(i × t) for `i` imports of units of size `t`. Used: a memo by unit index, each unit
/// addressed once, O(t log t) for the units' definitions in all. Tradeoffs: one address kept
/// per unit while the pins are checked. COMPLEXITY.md row F129.
fn unit_address(
    db: &mut Db,
    pkg: &Package,
    memo: &mut [Option<Arc<pin::Address>>],
    v: usize,
) -> Arc<pin::Address> {
    if let Some(a) = &memo[v] {
        return a.clone();
    }
    let u = &pkg.units[v];
    let a = match (&u.text, &u.resolved) {
        (Some(Ok(text)), Some(r)) => db.address(text, &r.res.exports),
        _ => Arc::new(None),
    };
    memo[v] = Some(a.clone());
    a
}

/// The rejection at `span` of a pin of the unit `path`, whose address zedc could not compute
/// for want of memory, `too` saying how much.
fn too_large(span: Span, path: &str, too: &zed_kernel::num::TooLarge) -> Error {
    error(
        span,
        format!(
            "zedc could not compute the content address of the unit `{path}`, which the build \
             pins here: one of its constants takes {} bytes, and the system refused zedc that \
             much memory to write the constant out. The program is not wrong. Repair: free \
             memory and build again.",
            too.bytes()
        ),
    )
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

/// What `zedc run` reports of the package of the unit `file`, read as `text` and lying at
/// `place`: `None` when the unit compiles alone, since it has no manifest above it, or it
/// imports nothing and its manifest names no prelude unit; otherwise each problem of the
/// package its unit reaches, the files written under the root as `file`'s directory names it,
/// with its address, and a line for each problem whose address `suppress` names
/// ([`Package::report_on_disk`]), after the pins the build writes are written into the files
/// ([`Package::write_pins`]), followed by each file they could not be written into.
pub fn package_report(
    file: &Path,
    place: Place,
    text: &str,
    suppress: &mut Suppress,
) -> Result<Option<Vec<String>>, String> {
    let Place::Unit { root, name } = place else {
        return Ok(None);
    };
    let mut db = Db::new();
    let imports = matches!(&*db.parse(text), Ok((_, i)) if !i.is_empty());
    let dir = Dir(root);
    let prelude = match dir.read(MANIFEST) {
        Some(Ok(m)) => !matches!(manifest(&m), Ok(Manifest { prelude: None })),
        _ => true,
    };
    if !imports && !prelude {
        return Ok(None);
    }
    let path = unit_of(&name)?;
    let pkg = load(&mut db, &dir, &[&path]);
    // The root as the command line reached it: the file's directory, and up from there.
    let depth = path.matches('.').count();
    let shown = file.parent().and_then(|p| p.ancestors().nth(depth));
    let shown = shown.unwrap_or(&dir.0);
    // The pins are written before anything is reported, so that a build stopped by another
    // problem still pins the imports it could.
    let failed = pkg.write_pins(&dir.0, shown);
    let mut report = pkg.report_on_disk(shown, suppress);
    report.extend(failed);
    Ok(Some(report))
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

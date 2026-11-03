//! The M0.4 layer checker. `layer SPEC_DIR [-v] PROGRAM.zed ...` fails if any program disagrees.
//!
//! For each program (a main file NN-name.zed plus every .zed file under the directory NN-name/,
//! its other units) it prints
//!
//! ```text
//! the parse ring   lowest ring at which every unit parses
//! the table layer  highest layer of a defined word the program uses, read from the table
//!                  "Defined words by layer" in DESIGN.md, with the word that sets it
//! the label        the `// layer Lk` comment on the main file's first line
//! enabled          max(parse ring, table layer, label)  (M0.4, condition 3)
//! agree            enabled == label
//! ```
//!
//! and flags a program whose label is above both mechanical layers, since then the label alone
//! sets its layer (the reason must be in LEDGER.md).
//!
//! Scope pass. A word is a use of the prelude only where it resolves to the prelude: a name the
//! program binds anywhere, in any unit, shadows the table word. Binding positions: function,
//! method, parameter, lambda parameter, binding target, indexed-definition name and index key,
//! boundary item, signature, struct, field, type, type parameter, interface, law, import names,
//! pattern names, `for` binders, loop labels, record-display labels and grammar field labels.
//! Port names are the environment's, not the program's, and the `log` port counts as the
//! table's L7 word. Labels that are neither uses nor bindings: named arguments and
//! `with { f = … }` field paths.
//!
//! Positions. An annotation counts wherever it appears. A facet word counts only as the name in
//! `with name(…)`; a facet name the table does not list is a user facet (L12). A `::x` entry
//! counts only as a `::` read. A target value (#cpu, #wasm, #gpu, #cluster) counts only as an
//! argument of `target(…)` or as `@require`'s `target:`. Every other atom of the table counts
//! only where a program reads it: in a pattern or a type (an atom the program constructs is an
//! ordinary atom). Every other table word counts as any unshadowed use.
//!
//! Known limits (no types here): `.fold` on a recursive union (L6) is not told apart from `fold`
//! (L3); `abs` on the number algebras (L14) is not told apart from `abs` on scalars; unlisted
//! prelude functions on families (L3) are not counted. These are reported in LEDGER.md for the
//! programs they touch.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

use zedc::parse::{Kind, Parser, TOP};

use crate::ring::ring_of;
use crate::spec::Spec;
use crate::syntax::{Tokens, Tree, lex, then_end};
use crate::text::{base_name, left, read_text, repr, right, strip};
use crate::{Outcome, arg, say};

const TARGET_ATOMS: [&str; 4] = ["#cpu", "#wasm", "#gpu", "#cluster"];

/// Words the table names in prose rather than in backticks.
fn prose_words(layer: u32) -> &'static [&'static str] {
    match layer {
        13 => &["sanitize"], // "the sanitizers" (sec:tour_grammar: sanitize(…))
        20 => &["serialize", "Json", "Csv"], // "the serializers, JSON and CSV"
        _ => &[],
    }
}

/// Backtick spans that need types to tell apart, so are not counted.
const UNCOUNTED: [&str; 2] = [".fold", "abs"];

/// The non-empty backtick spans of `s`.
fn spans(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(a) = rest.find('`') {
        let after = &rest[a + 1..];
        let Some(b) = after.find('`') else { break };
        if b == 0 {
            rest = after;
        } else {
            out.push(&after[..b]);
            rest = &after[b + 1..];
        }
    }
    out
}

/// Whether `w` is a plain ASCII word.
fn is_word(w: &str) -> bool {
    let mut cs = w.chars();
    cs.next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// The table "Defined words by layer" of `DESIGN.md`: word to layer for annotations, facets,
/// forms, suffix reads and atoms.
#[derive(Clone, Debug, Default)]
pub struct WordTable {
    annots: HashMap<String, u32>,
    facets: HashMap<String, u32>,
    forms: HashMap<String, u32>,
    reads: HashMap<String, u32>,
    atoms: HashMap<String, u32>,
}

impl WordTable {
    /// Reads the table of the document at `design`.
    pub fn read(design: &str) -> Result<WordTable, String> {
        let text = read_text(design)?;
        let mut lines = text
            .split('\n')
            .skip_while(|l| !l.starts_with("| Layer | Annotations | Facet words"));
        if lines.next().is_none() {
            return Err(format!("no table of defined words in {design}"));
        }
        let mut t = WordTable::default();
        for l in lines.skip(1).take_while(|l| l.starts_with('|')) {
            t.read_row(l)?;
        }
        t.forms.remove("log"); // the log port: counted as a port name, in `analyze`
        Ok(t)
    }

    fn read_row(&mut self, l: &str) -> Result<(), String> {
        let cols: Vec<&str> = strip(l).trim_matches('|').split('|').map(strip).collect();
        let [layer, c1, c2, c3, ..] = cols[..] else {
            return Err(format!("a table row with too few columns: {l}"));
        };
        let k: u32 = layer
            .trim_start_matches('L')
            .parse()
            .map_err(|_| format!("a table row with no layer: {l}"))?;
        for (col, cell) in [c1, c2, c3].into_iter().enumerate() {
            for w in spans(cell) {
                // A named argument (`nodes:`) is read with its call, which the row names, and a
                // call (`target(…)`) refers to a word its own row counts.
                let argument = w.strip_suffix(':').is_some_and(is_word);
                let call = w.strip_suffix("(…)").is_some_and(is_word);
                if UNCOUNTED.contains(&w) || w.starts_with("with ") || argument || call {
                    continue;
                }
                let (map, word) = if w.starts_with('@') {
                    (&mut self.annots, w)
                } else if w.starts_with('#') {
                    (&mut self.atoms, w)
                } else if let Some((_, tail)) = w.split_once("::") {
                    let word = tail.split("::").next().expect("split yields one item");
                    (&mut self.reads, word)
                } else if !is_word(w) {
                    return Err(format!("unparsed table span {}", repr(w)));
                } else if col == 1 {
                    (&mut self.facets, w)
                } else {
                    (&mut self.forms, w)
                };
                map.entry(word.into()).or_insert(k);
            }
        }
        for w in prose_words(k) {
            self.forms.entry((*w).into()).or_insert(k);
        }
        Ok(())
    }
}

/// A parse tree and the tokens its spans index.
#[derive(Clone, Debug)]
pub struct Parsed {
    /// The tree.
    pub tree: Tree,
    /// The tokens.
    pub toks: Tokens,
}

/// The tree of the hole text `h`, added to `trees`, with the holes inside it moved to `pending`.
fn add_hole(
    spec: &Spec,
    h: &str,
    pending: &mut Vec<String>,
    trees: &mut Vec<Parsed>,
) -> Result<(), String> {
    let mut ht = lex(&spec.lexical, h)?;
    let mut q = Parser::new(&spec.syntactic, TOP, &ht);
    let (_, root) = then_end(&spec.syntactic, &mut q, &ht, "Expr")
        .ok_or_else(|| format!("the hole {} does not parse", repr(h)))?;
    let nodes = q.nodes;
    pending.extend(ht.0.iter_mut().flat_map(|t| std::mem::take(&mut t.holes)));
    trees.push(Parsed {
        tree: Tree { nodes, root },
        toks: ht,
    });
    Ok(())
}

/// The trees of the `${…}` holes of `toks` and of the holes in those, added to `trees`, each
/// hole's inner holes right after it. A tree added here keeps its tokens without their holes.
pub fn add_holes(spec: &Spec, toks: &Tokens, trees: &mut Vec<Parsed>) -> Result<(), String> {
    let mut pending = Vec::new();
    for h in toks.0.iter().flat_map(|t| &t.holes).rev() {
        add_hole(spec, h, &mut pending, trees)?;
        while let Some(inner) = pending.pop() {
            add_hole(spec, &inner, &mut pending, trees)?;
        }
    }
    Ok(())
}

/// How a name, atom or facet occurs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Use,
    Bind,
    Port,
    Label,
    Facet,
    Read,
    AtomRead,
    TargetAtom,
}

/// A table word a program uses: its layer, the word, how it is used. The order is the order of
/// these fields.
pub type Hit = (u32, String, &'static str);

fn is_binder(rule: &str) -> bool {
    matches!(
        rule,
        "Function"
            | "Param"
            | "Target"
            | "Signature"
            | "Struct"
            | "StructField"
            | "Field"
            | "TypeDecl"
            | "TypeParams"
            | "Interface"
            | "Law"
            | "Binder"
            | "Loop"
            | "Display"
            | "FieldPat"
            | "BoundaryItem"
            | "IndexKey"
            | "TypedBinding"
            | "Lambda"
            | "PositionalParam"
            | "Import"
            | "Member"
            | "GItem"
            | "IsPat"
            | "NamePat"
    )
}

/// The role of the name at child `k` of a node of rule `rule`, and whether `k` is the node's
/// first name.
fn role(rule: &str, k: usize, first: bool, tree: &Tree, toks: &Tokens) -> Role {
    match rule {
        r if is_binder(r) => Role::Bind,
        "IndexedDef" if first => Role::Bind,
        "Method" if !first => Role::Bind,
        "Port" => Role::Port,
        "NamedArg" | "Update" | "KeyPath" => Role::Label,
        "Refinement" if first => Role::Label,
        "ShapeDim" if toks.0[tree.node(k).end].text == ":" => Role::Label,
        "FacetCall" => Role::Facet,
        "ReadSuffix" => Role::Read,
        _ => Role::Use,
    }
}

/// Appends (role, word) for every name, atom and facet in `p`.
fn occurrences<'t>(spec: &Spec, p: &'t Parsed, out: &mut Vec<(Role, &'t str)>) {
    let (tree, toks) = (&p.tree, &p.toks);
    let name_of = |n: usize| toks.0[tree.node(n).start].text.as_str();
    let rule_of = |n: usize| spec.all.rules[tree.node(n).rule].name.as_str();
    // covered[i] counts the spans starting at or before token i, less those ended by then, of
    // the targets: each `target(…)` facet and each `target:` argument of an `@require`.
    let mut covered = vec![0i64; toks.0.len() + 1];
    let root_parent = "";
    let mut stack = vec![(tree.root, root_parent, false)];
    while let Some((n, parent, in_require)) = stack.pop() {
        let (node, rule) = (tree.node(n), rule_of(n));
        // A module path, not a use.
        if rule == "Path" && matches!(parent, "Import" | "Field" | "Pin" | "Member") {
            continue;
        }
        let mut first = true;
        for &k in &node.kids {
            if rule_of(k) == "Name" {
                out.push((role(rule, k, first, tree, toks), name_of(k)));
                first = false;
            }
        }
        let t = &toks.0[node.start.min(toks.0.len() - 1)];
        if matches!(rule, "AtomPattern" | "AtomType" | "AtomApply") && t.kind == Kind::Atom {
            out.push((Role::AtomRead, &t.text));
        }
        let first_is_target = node.kids.first().is_some_and(|&k| name_of(k) == "target");
        if first_is_target && (rule == "FacetCall" || (rule == "NamedArg" && in_require)) {
            covered[node.start] += 1;
            covered[node.end] -= 1;
        }
        let require = in_require || (rule == "Annot" && t.text == "@require");
        stack.extend(node.kids.iter().map(|&k| (k, rule, require)));
    }
    let mut depth = 0;
    for (t, change) in toks.0.iter().zip(&covered) {
        depth += change;
        if depth > 0 && t.kind == Kind::Atom {
            out.push((Role::TargetAtom, &t.text));
        }
    }
}

/// The table words `trees` use.
pub fn analyze(spec: &Spec, trees: &[Parsed], table: &WordTable) -> BTreeSet<Hit> {
    let mut occ = Vec::new();
    for p in trees {
        occurrences(spec, p, &mut occ);
    }
    let bound: HashSet<&str> = occ
        .iter()
        .filter(|(role, _)| *role == Role::Bind)
        .map(|(_, w)| *w)
        .collect();
    let mut hits = BTreeSet::new();
    for p in trees {
        let span = &p.toks.0[p.tree.node(p.tree.root).start..p.tree.node(p.tree.root).end];
        for t in span.iter().filter(|t| t.kind == Kind::Annot) {
            if let Some(&k) = table.annots.get(&t.text) {
                hits.insert((k, t.text.clone(), "annotation"));
            }
        }
    }
    let form = |w: &str| table.forms.get(w).copied().filter(|_| !bound.contains(w));
    for &(role, w) in &occ {
        let hit = match role {
            Role::Use if w == "log" && !bound.contains("log") => {
                Some((7, w.to_string(), "the log port"))
            }
            Role::Use => form(w).map(|k| (k, w.to_string(), "form")),
            Role::Read => table.reads.get(w).map(|&k| (k, format!("::{w}"), "read")),
            Role::Facet => Some(match (table.facets.get(w), form(w)) {
                (Some(&k), _) => (k, w.to_string(), "facet"),
                (None, Some(k)) => (k, w.to_string(), "facet word"),
                (None, None) => (12, w.to_string(), "user facet"),
            }),
            Role::Port if w == "log" => Some((7, w.to_string(), "the log port")),
            Role::AtomRead if !TARGET_ATOMS.contains(&w) => {
                table.atoms.get(w).map(|&k| (k, w.to_string(), "atom read"))
            }
            Role::TargetAtom => table
                .atoms
                .get(w)
                .map(|&k| (k, w.to_string(), "target value")),
            Role::Bind | Role::Port | Role::Label | Role::AtomRead => None,
        };
        hits.extend(hit);
    }
    hits
}

/// The layer named by the `// layer Lk` comment that `s` starts with.
pub fn label_at(s: &str) -> Option<u32> {
    let digits = s.strip_prefix("// layer L")?;
    let end = digits
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(digits.len());
    let ends_word = digits[end..]
        .chars()
        .next()
        .is_none_or(|c| !c.is_alphanumeric() && c != '_');
    if ends_word {
        digits[..end].parse().ok()
    } else {
        None
    }
}

/// Lists the entries of `dir`: the files, and the directories that are not symbolic links. A
/// symbolic link to a directory is neither.
fn list(dir: &str) -> Result<(Vec<String>, Vec<String>), String> {
    let (mut files, mut dirs) = (Vec::new(), Vec::new());
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{dir}: {e}"))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("{dir}: {e}"))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let path = format!("{dir}/{name}");
        let linked = entry.path().is_symlink();
        match (Path::new(&path).is_dir(), linked) {
            (true, true) => {}
            (true, false) => dirs.push(path),
            (false, _) => files.push(name),
        }
    }
    Ok((files, dirs))
}

/// The units of the program whose main file is `main`: it, then every .zed file under the
/// directory of its name without `.zed`, directory by directory in path order.
pub fn program_units(main: &str) -> Result<Vec<String>, String> {
    let mut units = vec![main.to_string()];
    let root = main.strip_suffix(".zed").unwrap_or(main);
    if !Path::new(root).is_dir() {
        return Ok(units);
    }
    let mut dirs = Vec::new();
    let mut pending = vec![root.to_string()];
    while let Some(dir) = pending.pop() {
        let (files, subdirs) = list(&dir)?;
        pending.extend(subdirs);
        dirs.push((dir, files));
    }
    dirs.sort();
    for (dir, mut files) in dirs {
        files.sort();
        units.extend(
            files
                .iter()
                .filter(|f| f.ends_with(".zed"))
                .map(|f| format!("{dir}/{f}")),
        );
    }
    Ok(units)
}

/// A program's layers.
struct Layered {
    units: usize,
    ring: u32,
    table: u32,
    word: String,
    enabled: u32,
    /// Every table word the program uses, lowest first.
    hits: BTreeSet<Hit>,
}

/// The layers of the program `main`, or why it has none; and its label.
fn check(
    spec: &Spec,
    table: &WordTable,
    main: &str,
) -> Result<(Option<u32>, Result<Layered, String>), String> {
    let paths = program_units(main)?;
    let mut label = None;
    let (mut trees, mut rng, mut whys) = (Vec::new(), 0, Vec::new());
    for (i, path) in paths.iter().enumerate() {
        let text = read_text(path)?;
        if i == 0 {
            label = label_at(&text);
        }
        match ring_of(spec, &text) {
            Ok(r) => {
                rng = rng.max(r.ring);
                add_holes(spec, &r.toks, &mut trees)?;
                trees.push(Parsed {
                    tree: r.tree,
                    toks: r.toks,
                });
            }
            Err(why) => whys.push(format!("{}: {why}", base_name(path))),
        }
    }
    if !whys.is_empty() {
        return Ok((label, Err(whys.join("; "))));
    }
    let hits = analyze(spec, &trees, table);
    let (tl, word) = hits
        .last()
        .map_or((1, "-".to_string()), |(k, w, _)| (*k, w.clone()));
    let verdict = Layered {
        units: paths.len(),
        ring: rng,
        table: tl,
        word,
        enabled: rng.max(tl).max(label.unwrap_or(0)),
        hits,
    };
    Ok((label, Ok(verdict)))
}

/// Writes the report on `files`, and says whether every program agrees.
pub fn report(spec: &Spec, verbose: bool, files: &[&str], out: &mut String) -> Outcome {
    let table = WordTable::read(&spec.design)?;
    let mut fails = 0;
    say!(
        out,
        "{} {} {} {} {} {} agree",
        left("program", 34),
        right("units", 5),
        right("ring", 5),
        left("table (word)", 16),
        right("label", 5),
        right("enabled", 7)
    );
    for f in files {
        let (label, verdict) = check(spec, &table, f)?;
        let name = left(base_name(f), 34);
        let r = match verdict {
            Ok(r) => r,
            Err(why) => {
                say!(out, "{name} PARSE FAIL {why}");
                fails += 1;
                continue;
            }
        };
        let agree = label == Some(r.enabled);
        let above = label.is_some_and(|l| l > r.ring.max(r.table));
        let lab = label
            .filter(|l| *l != 0)
            .map_or("none".to_string(), |l| format!("L{l}"));
        let tag = match (agree, above) {
            (true, true) => "yes (label above ring and table)",
            (true, false) => "yes",
            (false, _) => "NO",
        };
        say!(
            out,
            "{name} {} {} {} {} {} {tag}",
            right(&r.units.to_string(), 5),
            right(&format!("L{}", r.ring), 5),
            left(&format!("L{} ({})", r.table, r.word), 16),
            right(&lab, 5),
            right(&format!("L{}", r.enabled), 7)
        );
        if verbose {
            for (k, w, how) in r.hits.iter().rev() {
                say!(
                    out,
                    "      L{} {} {how}",
                    left(&k.to_string(), 3),
                    left(w, 14)
                );
            }
        }
        fails += usize::from(!agree);
    }
    Ok(fails == 0)
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "layer SPEC_DIR [-v] PROGRAM.zed ...")?)?;
    let rest = &args[1..];
    let files: Vec<&str> = rest
        .iter()
        .map(String::as_str)
        .filter(|a| *a != "-v")
        .collect();
    report(&spec, rest.iter().any(|a| a == "-v"), &files, out)
}

#[cfg(test)]
mod tests {
    use super::WordTable;

    /// A named argument such as `nodes:` is read with its call, and a call such as `target(…)`
    /// refers to a word another row counts, so a row names both without counting them; any
    /// other span that is not a word is still refused.
    #[test]
    fn argument_names_are_not_counted() {
        let mut t = WordTable::default();
        t.read_row("| L27 | — | `recovery` | the target values `#gpu` and `#cluster`; the size `nodes:` of `target(…)` and `@require` |")
            .unwrap();
        assert_eq!(t.facets.get("recovery"), Some(&27));
        assert_eq!(t.atoms.get("#cluster"), Some(&27));
        assert!(!t.forms.contains_key("nodes") && !t.forms.contains_key("nodes:"));
        assert!(!t.forms.contains_key("target") && !t.forms.contains_key("target(…)"));
        assert!(t.read_row("| L27 | — | — | `a b` |").is_err());
        assert!(t.read_row("| L27 | — | — | `:` |").is_err());
    }
}

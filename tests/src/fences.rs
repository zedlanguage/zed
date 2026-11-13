//! The documentation's fences, each with its layer: those of DESIGN.md and EXAMPLES.md, read
//! from the spec in place (`crate::spec`), and those of this repository's README.md, laid out
//! against the spec's grammar (`zed_tools::fence_layers`); and the hand-written fixtures of
//! their commented ✗ variants, in `zed/fences/variants/`. No copy of the spec is kept in this
//! repository.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use zed_tools::fence_layers::{self, LaidFence};
use zed_tools::spec::Spec;
use zedc::fence;

/// A fence of DESIGN.md, EXAMPLES.md or README.md, with its layer.
#[derive(Clone, Debug)]
pub struct DocFence {
    /// Its document, section and place among the fences of that section: `DESIGN.md
    /// [sec:remap_law] 1`. Expected outputs are keyed by it, so that an edit in one section of
    /// the document changes no other section's keys.
    pub key: String,
    /// The document and line of its ```` ```zed ````, for messages: `DESIGN.md:196`.
    pub at: String,
    /// The layer from which it is parsed, checked and run.
    pub layer: u32,
    /// The lowest ring of sec:grammar at which it parses.
    pub ring: u32,
    /// Whether it parses only under the documentation notation of sec:grammar.
    pub notation: bool,
    /// Its text.
    pub text: String,
}

impl From<LaidFence> for DocFence {
    fn from(l: LaidFence) -> DocFence {
        let f = l.fence;
        DocFence {
            key: format!("{} [{}] {}", f.file, f.section, f.index),
            at: format!("{}:{}", f.file, f.line),
            layer: l.layer,
            ring: l.ring,
            notation: l.notation,
            text: f.text,
        }
    }
}

/// A rejected variant: a fence with one commented ✗ line made live.
#[derive(Clone, Debug)]
pub struct Variant {
    /// The fixture's file name, without `.zed`.
    pub name: String,
    /// The commented line of the fence it is a variant of, trimmed.
    pub of: String,
    /// The fixture's text, its first line, `// variant: …`, included.
    pub text: String,
}

/// The directory `zed/fences/`, which holds the variant fixtures and the predictions.
pub fn dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/fences")
}

/// The fences of the document at `path`, laid out against `spec`, in order.
pub fn of_document(path: &Path, spec: &Spec) -> Vec<DocFence> {
    let path = path.to_str().expect("a UTF-8 path");
    fence_layers::of_document(path, spec)
        .unwrap_or_else(|e| panic!("{e}"))
        .into_iter()
        .map(DocFence::from)
        .collect()
}

/// The spec's grammars and its directory, read once per test binary. Panics where the spec is
/// not found, or where `ZED_SPEC_DIR=none` says not to read it.
pub fn spec() -> &'static Spec {
    static SPEC: OnceLock<Spec> = OnceLock::new();
    SPEC.get_or_init(|| {
        let root = crate::spec::dir("the documentation's fences").unwrap_or_else(|| {
            panic!(
                "the fences of DESIGN.md and EXAMPLES.md and the grammar are read from the spec \
                 repository, and {}={} says not to read it",
                crate::spec::VAR,
                crate::spec::NONE
            )
        });
        Spec::open(root.to_str().expect("a UTF-8 path")).unwrap_or_else(|e| panic!("{e}"))
    })
}

/// The fences of `doc` under the directory `under`, laid out once per test binary in `cell`.
/// Laying out a fence parses it at up to every ring, which over a whole document takes about a
/// second, so each document is laid out once.
fn laid(cell: &'static OnceLock<Vec<DocFence>>, under: &str, doc: &str) -> Vec<DocFence> {
    cell.get_or_init(|| of_document(&Path::new(under).join(doc), spec()))
        .clone()
}

/// The fences of DESIGN.md, in order.
pub fn design() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(&CELL, &spec().root, "DESIGN.md")
}

/// The fences of EXAMPLES.md, in order.
pub fn examples() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(&CELL, &spec().root, "EXAMPLES.md")
}

/// Every fence: DESIGN.md's, then EXAMPLES.md's.
pub fn all() -> Vec<DocFence> {
    let mut out = design();
    out.extend(examples());
    out
}

/// The fences of this repository's README.md (item README-fences), in order, laid out against
/// the spec's grammar. They are not among [`all`]: the page states its own results, and its
/// tests compare them with the run.
pub fn readme() -> Vec<DocFence> {
    static CELL: OnceLock<Vec<DocFence>> = OnceLock::new();
    laid(
        &CELL,
        concat!(env!("CARGO_MANIFEST_DIR"), "/.."),
        "README.md",
    )
}

/// Every variant fixture, by name.
pub fn variants() -> Vec<Variant> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir().join("variants"))
        .expect("the variants directory")
        .map(|e| e.expect("an entry").path())
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|p| {
            let text = std::fs::read_to_string(&p).expect("a readable fixture");
            let of = text
                .lines()
                .next()
                .and_then(|l| l.strip_prefix("// variant: "))
                .unwrap_or_else(|| panic!("{} has no `// variant:` line", p.display()))
                .into();
            Variant {
                name: p.file_stem().expect("a name").to_string_lossy().into(),
                of,
                text,
            }
        })
        .collect()
}

/// A way a variant fixture differs from its fence other than the commented ✗ line it makes
/// live. The test names each one, so that every other line of a fixture follows its fence.
#[derive(Clone, Copy, Debug)]
pub enum Change {
    /// The fixture writes `line` where the fence writes `stands_for`.
    Stands {
        /// The fixture's name, without `.zed`.
        fixture: &'static str,
        /// The fixture's line, as written.
        line: &'static str,
        /// The fence's line, as written.
        stands_for: &'static str,
    },
    /// The fixture leaves out each line of the fence written `line` that it does not copy.
    Omits {
        /// The fixture's name, without `.zed`.
        fixture: &'static str,
        /// The fence's line, as written.
        line: &'static str,
    },
}

impl Change {
    /// The fixture it belongs to.
    fn fixture(&self) -> &'static str {
        match self {
            Change::Stands { fixture, .. } | Change::Omits { fixture, .. } => fixture,
        }
    }
}

/// The ways the fixtures in `zed/fences/variants/` differ from their fences.
pub const CHANGES: &[Change] = &[
    // A constructor call by position beside the call by name would bind q twice.
    Change::Omits {
        fixture: "constructor-called-by-position",
        line: "q = Point(x:, y:);                 // Point(x: x, y: y)",
    },
    // The fence's variants each replace the line `prev = c*.bump(3);`, as its comment says, and
    // no ✗ variant binds `prev`, so `until prev > 20` would read a name no line binds, and the
    // fixture would fail on that line as well as on its ✗ line.
    Change::Omits {
        fixture: "dot-never-mutates",
        line: "  prev = c*.bump(3);                // `*.` calls and mutates: writes c', yields the return",
    },
    Change::Stands {
        fixture: "dot-never-mutates",
        line: "  until c.n > 20;                    //   — one write of c' per step, as always",
        stands_for: "  until prev > 20;                  //   — one write of c' per step, as always",
    },
    Change::Omits {
        fixture: "two-writers-of-one-generation",
        line: "  prev = c*.bump(3);                // `*.` calls and mutates: writes c', yields the return",
    },
    Change::Stands {
        fixture: "two-writers-of-one-generation",
        line: "  until c.n > 20;                    //   — one write of c' per step, as always",
        stands_for: "  until prev > 20;                  //   — one write of c' per step, as always",
    },
    // The two commented field lines are edits of the field types of `orders`, not lines of
    // their own: each fixture edits the declaration and keeps the commented lines.
    Change::Stands {
        fixture: "nullable-column-missing-none",
        line: "orders: OrderId ->? { total: rat, note: Utf8String }   // ✗ Stored collection whose \
               type and schema disagree: the column is nullable, and #none is missing from the \
               field type",
        stands_for: "orders: OrderId ->? { total: rat, note: Utf8String | #none }",
    },
    Change::Stands {
        fixture: "numeric-is-not-binary-float",
        line: "orders: OrderId ->? { total: f64, note: Utf8String | #none }   // ✗ Stored \
               collection whose type and schema disagree: NUMERIC is not a binary float",
        stands_for: "orders: OrderId ->? { total: rat, note: Utf8String | #none }",
    },
    // The fixture keeps the one binding the ✗ line reads and leaves out the others and the
    // live ✗ line.
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "q   = 7 div 2;             // 3      integers divide with div and mod (Euclidean)",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "r   = -7 mod 2;            // 1      (-7) mod 2 — unary minus binds tighter than \
               mod; the remainder is never negative",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "h   = f64(7) / 2;          // 3.5    a cast is the type applied to the value",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "t   = 1r / 3r;             // exact: rat",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "big = 2^100;              // int has no width; ^ binds tighter than * and than \
               unary minus, and associates to the right",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "m   = 1_000_000;  hex = 0xFF;  bits = 0b1011;  sci: f64 = 1.5e-3;",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "half: f64 = 0.5;           // never .5: a float literal starts with a digit; a \
               decimal literal takes the format its use fixes, here the declared f64, and one \
               that nothing fixes is an error; a suffix, as in 0.5f64, forces the format",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "dbl = h * 2;               // 7.0    h is an f64, and the literal 2 takes the \
               carrier of the other operand",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "y   = x^2 + 2*x + 1;",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "b: u8 = 255;               // u8 = int[0..=255]; 256 here is a type error, not a \
               wrap",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "w: i32 = shl(1, 30);       // no bitwise operators: bitAnd, bitOr, shl are \
               ordinary functions",
    },
    Change::Omits {
        fixture: "decimal-literal-at-int",
        line: "z   = 7 / 2;               // ✗ Decimal literal, or `/` of integer literals, \
               that nothing gives a carrier: `/` is for the float formats and rat only, so 7 and \
               2 stay without one; write f64(7) / 2 or declare z: f64",
    },
    // The sanitized call beside the ✗ call would bind rows twice.
    Change::Omits {
        fixture: "taint-through-concatenation",
        line: "rows = exec(db, \"SELECT * WHERE name = \" ++ sanitize(userName));  // ✓ and the \
               sanitizer is auditable",
    },
    // The ✗ line takes the place of the return that reads t.
    Change::Omits {
        fixture: "block-binding-never-read",
        line: "  return s + t;",
    },
];

/// Where each of `variants` disagrees with the fence of `fences` whose commented ✗ line it
/// makes live, one message for each fixture that agrees with none of the fences holding its
/// line. A fixture agrees with a fence when, after its `// variant:` line, it is the fence's
/// lines in order with these differences only: its live ✗ line takes the place of the
/// fence's commented ✗ line, the two equal once the `//` is removed and runs of white space
/// are read as one space, and `changes` names each other difference. A live ✗ line that
/// stands for another line by `changes` edits that line instead, and the commented line stays.
/// Also named: a change a fixture that agrees does not use, a change of no fixture, and a
/// commented ✗ line that several fences hold and no fixture agrees with in one of them.
///
/// The fences holding a line are found by hashing, and a fixture is read once along each
/// fence holding its line, so the cost is linear in the lines of the fences, the fixtures and
/// the changes, times the number of fences holding one commented ✗ line (one in the
/// documents).
pub fn disagreements(fences: &[DocFence], variants: &[Variant], changes: &[Change]) -> Vec<String> {
    use std::collections::{HashMap, HashSet};

    let lines: Vec<Vec<&str>> = fences
        .iter()
        .map(|f| f.text.split('\n').collect())
        .collect();
    // Each commented ✗ line, trimmed, with the fences and lines (from 0) that hold it.
    let mut places: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();
    for (i, f) in fences.iter().enumerate() {
        for k in fence::marks(&f.text).variants {
            places
                .entry(lines[i][k - 1].trim())
                .or_default()
                .push((i, k - 1));
        }
    }
    let mut by_fixture: HashMap<&str, Vec<usize>> = HashMap::new();
    for (c, change) in changes.iter().enumerate() {
        by_fixture.entry(change.fixture()).or_default().push(c);
    }
    let mut used = vec![false; changes.len()];
    let mut agreed: HashSet<(usize, usize)> = HashSet::new();
    let mut failed: HashSet<&str> = HashSet::new();
    let mut out = Vec::new();
    for v in variants {
        let live = fence::marks(&v.text).lines;
        let [live] = live[..] else {
            out.push(format!(
                "{}.zed has {} live ✗ lines, not one",
                v.name,
                live.len()
            ));
            continue;
        };
        let Some(held) = places.get(v.of.as_str()) else {
            out.push(format!(
                "{}.zed: its `// variant:` line is the commented ✗ line of no fence: {}",
                v.name, v.of
            ));
            continue;
        };
        let body: Vec<&str> = v.text.split('\n').skip(1).collect();
        let body = match body.split_last() {
            Some((&"", rest)) => rest,
            _ => &body[..],
        };
        let mine = Mine::of(
            changes,
            by_fixture.get(v.name.as_str()).map_or(&[], |c| &c[..]),
        );
        let mut first = None;
        let mut agrees = false;
        for &(i, k) in held {
            match mine.place(body, live - 2, &lines[i], k) {
                Ok(uses) => {
                    agreed.insert((i, k));
                    agrees = true;
                    for c in uses {
                        used[c] = true;
                    }
                }
                Err(why) => {
                    first.get_or_insert_with(|| {
                        format!("{}.zed:{why}; its fence is at {}", v.name, fences[i].at)
                    });
                }
            }
        }
        if agrees {
            for &c in by_fixture.get(v.name.as_str()).map_or(&[][..], |c| &c[..]) {
                if !used[c] {
                    out.push(format!(
                        "{}.zed does not use the change {:?}",
                        v.name, changes[c]
                    ));
                }
            }
        } else {
            failed.insert(v.of.as_str());
            out.extend(first);
        }
    }
    let names: HashSet<&str> = variants.iter().map(|v| v.name.as_str()).collect();
    for change in changes {
        if !names.contains(change.fixture()) {
            out.push(format!("no fixture has the change {change:?}"));
        }
    }
    for (line, held) in &places {
        if held.len() > 1 && !failed.contains(line) {
            for &(i, k) in held {
                if !agreed.contains(&(i, k)) {
                    out.push(format!(
                        "{}: no fixture agrees with the fence's commented ✗ line {}: {line}",
                        fences[i].at,
                        k + 1
                    ));
                }
            }
        }
    }
    out.sort();
    out
}

/// The changes of one fixture, by its line for a stand and by the fence's line for an omission,
/// each with its place in the list of changes.
struct Mine<'a> {
    stands: std::collections::HashMap<&'a str, (&'a str, usize)>,
    omits: std::collections::HashMap<&'a str, usize>,
}

impl<'a> Mine<'a> {
    /// The changes `which` of `changes`.
    fn of(changes: &'a [Change], which: &[usize]) -> Self {
        let mut mine = Mine {
            stands: Default::default(),
            omits: Default::default(),
        };
        for &c in which {
            match changes[c] {
                Change::Stands {
                    line, stands_for, ..
                } => {
                    mine.stands.insert(line, (stands_for, c));
                }
                Change::Omits { line, .. } => {
                    mine.omits.insert(line, c);
                }
            }
        }
        mine
    }

    /// Whether the fixture lines `body`, whose line `live` (from 0) is its live ✗ line, are the
    /// fence `lines` with its commented line `k` (from 0) made live and these changes made: the
    /// changes used, or the first fixture line (counted as in its file) that differs, and how.
    fn place(
        &self,
        body: &[&str],
        live: usize,
        lines: &[&str],
        k: usize,
    ) -> Result<Vec<usize>, String> {
        // A live line that stands for another line of the fence makes the variant by editing
        // that line, and the fence's commented line stays as it is; any other live line takes
        // the commented line's place.
        let anchored = !self.stands.contains_key(body[live]);
        let mut uses = Vec::new();
        let mut j = 0;
        for (p, &want) in lines.iter().enumerate() {
            if anchored && p == k {
                let uncommented = want.trim_start().strip_prefix("//").unwrap_or(want);
                if j != live
                    || !body[live]
                        .split_whitespace()
                        .eq(uncommented.split_whitespace())
                {
                    return Err(format!(
                        "{}: the fence's line {} made live belongs here: {}",
                        j + 2,
                        k + 1,
                        uncommented.trim()
                    ));
                }
                j += 1;
                continue;
            }
            let got = body.get(j).filter(|_| !(anchored && j == live)).map(|&l| {
                match self.stands.get(l) {
                    Some(&(stands_for, c)) => (stands_for, Some(c)),
                    None => (l, None),
                }
            });
            match got {
                Some((l, c)) if l == want => {
                    uses.extend(c);
                    j += 1;
                }
                _ => match self.omits.get(want) {
                    Some(&c) => uses.push(c),
                    None => {
                        let at = match body.get(j) {
                            Some(l) => format!("{}: `{}`", j + 2, l.trim()),
                            None => format!("{}: the file ends", j + 2),
                        };
                        return Err(format!(
                            "{at} where the fence's line {} is: `{}`",
                            p + 1,
                            want.trim()
                        ));
                    }
                },
            }
        }
        match body.get(j) {
            Some(l) => Err(format!(
                "{}: `{}` after the fence's last line",
                j + 2,
                l.trim()
            )),
            None => Ok(uses),
        }
    }
}

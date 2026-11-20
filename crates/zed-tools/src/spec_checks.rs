//! Readers and checks of the spec's prose, which this repository does not hold: the `sync`
//! tool runs the checks on the spec checkout, the tests built with the feature `spec` run the
//! readers and the checks on DESIGN.md in place, and the tests run both on small documents of their own.
//! [`kernel_rules`] gives the names no message prints; [`serial_tables`] gives the tables of
//! step M0.7's serialization; [`prelude_laws`] compares the prelude laws DESIGN.md states with
//! `docs/mathlib-study.md`; [`build_modes`] checks the "Build modes" bullet and every kind of
//! build DESIGN.md names (plan row BUILD-modes).

use std::collections::BTreeSet;
use std::fmt::Write;

/// The header of each table of step M0.7's serialization ends with this text.
pub const SERIAL_HEADER: &str = " | Tag | Fields in order |";

/// The header of step M0.7's table of the primitives' codes.
pub const PRIM_HEADER: &str = "| Primitive | Code |";

/// The tables of step M0.7's serialization, each a table of DESIGN.md whose header ends with
/// [`SERIAL_HEADER`] or is [`PRIM_HEADER`]: its header and rows as written, without the line
/// under the header, the tables one after another. O(size of `design`).
pub fn serial_tables(design: &str) -> String {
    let mut out = String::new();
    let mut lines = design.lines();
    while let Some(line) = lines.next() {
        if !((line.starts_with("| ") && line.ends_with(SERIAL_HEADER)) || line == PRIM_HEADER) {
            continue;
        }
        writeln!(out, "{line}").expect("writing to a String");
        for row in lines.by_ref().skip(1).take_while(|l| l.starts_with("| ")) {
            writeln!(out, "{row}").expect("writing to a String");
        }
    }
    out
}

/// The words no message prints (DESIGN.md sec:diagnostics), sorted: the name of each typing
/// rule of the kernel calculus, `T-` and the generator for each generator of sec:kernel's
/// grammar `F ::= …` (`fam` gives `T-Fam`), with every other `T-` rule the spec names; and
/// `Boom`, since a menu says a reduction owes its operator's laws, not its Boom obligations
/// (item MSG-words). One pass over `design`.
pub fn kernel_rules(design: &str) -> Result<Vec<String>, String> {
    let kernel = design
        .split_once("\n# (sec:kernel)")
        .ok_or("DESIGN.md has no section sec:kernel")?
        .1;
    let kernel = kernel.split_once("\n# (").map_or(kernel, |(k, _)| k);
    let mut words = BTreeSet::from(["Boom".to_string()]);
    let mut generators = 0;
    for line in kernel.lines() {
        let Some(rest) = line
            .strip_prefix("F ::= ")
            .or_else(|| line.trim_start().strip_prefix("| "))
        else {
            continue;
        };
        let Some((name, _)) = rest.split_once('(') else {
            continue;
        };
        let mut chars = name.chars();
        let Some(first) = chars.next().filter(|c| c.is_ascii_lowercase()) else {
            continue;
        };
        let rest = chars.as_str();
        if rest.chars().all(|c| c.is_ascii_alphanumeric()) {
            words.insert(format!("T-{}{rest}", first.to_ascii_uppercase()));
            generators += 1;
        }
    }
    // The grammar names seven generators; a parse that found none would ban nothing.
    if generators < 7 {
        return Err(format!(
            "sec:kernel's grammar has {generators} generators, not seven or more"
        ));
    }
    for (at, _) in design.match_indices("T-") {
        let before = design[..at].chars().next_back();
        let rule: String = design[at + 2..]
            .chars()
            .take_while(|c| c.is_alphanumeric())
            .collect();
        if !before.is_some_and(|c| c.is_alphanumeric() || c == '_')
            && rule.starts_with(|c: char| c.is_uppercase())
        {
            words.insert(format!("T-{rule}"));
        }
    }
    Ok(words.into_iter().collect())
}

/// The laws of the prelude that `docs/mathlib-study.md` cites without writing them.
pub const PRELUDE: &[&str] = &["anyIntro", "anyElim", "allElim", "allIntro"];

/// The names in the first list of laws after `head` in `text`: each backquoted name up to the
/// `;` that ends the list.
fn named_after<'a>(text: &'a str, head: &str) -> Option<Vec<&'a str>> {
    let (_, rest) = text.split_once(head)?;
    let list = rest.split_once(';').map_or(rest, |(list, _)| list);
    Some(list.split('`').skip(1).step_by(2).collect())
}

/// Whether `design` names the laws of [`PRELUDE`] where step L15.7 builds them and where its
/// test says they reach proof grade, and states each in sec:verification, `allIntro` as `page`
/// (the mathlib study) writes it, without its proof (item MATHLIB-allintro-spec added
/// `allIntro`). The first difference otherwise.
pub fn prelude_laws(design: &str, page: &str) -> Result<(), String> {
    let step = design
        .lines()
        .find(|l| l.starts_with("L15.7. "))
        .ok_or("DESIGN.md has no step L15.7")?;
    let built = named_after(step, "the prelude laws ").ok_or("step L15.7 names no prelude laws")?;
    if built != PRELUDE {
        return Err(format!(
            "step L15.7 builds the prelude laws {built:?}, not {PRELUDE:?}"
        ));
    }
    let reach = step
        .split_once(" reach proof grade")
        .ok_or("step L15.7's test names no laws that reach proof grade")?
        .0;
    let reach = reach.rsplit_once(';').map_or(reach, |(_, r)| r);
    let reach: Vec<&str> = reach.split('`').skip(1).step_by(2).collect();
    if reach != PRELUDE {
        return Err(format!(
            "step L15.7's test brings {reach:?} to proof grade, not {PRELUDE:?}"
        ));
    }
    let states = design
        .lines()
        .find_map(|l| l.split_once("The prelude also states ").map(|(_, r)| r))
        .ok_or("DESIGN.md does not state the prelude laws")?;
    let states = states.split_once(". ").map_or(states, |(s, _)| s);
    if let Some(name) = PRELUDE
        .iter()
        .find(|n| !states.contains(&format!("`{n}`")) && !states.contains(&format!("law {n}(")))
    {
        return Err(format!("DESIGN.md does not state `{name}`"));
    }
    let written = page
        .lines()
        .find(|l| l.starts_with("law allIntro("))
        .and_then(|l| l.split_once(" proof {"))
        .ok_or("the mathlib study does not write `allIntro` with a proof")?
        .0;
    if !states.contains(&format!("`{written}`")) {
        return Err(format!(
            "DESIGN.md states `allIntro` otherwise than the mathlib study: `{written}`"
        ));
    }
    Ok(())
}

/// The words that come before "build" or "builds" in DESIGN.md and name no kind of build: a
/// determiner, a verb or adverb with "build" as a verb, a thing that builds something, a build
/// of one program or command, or a layer that builds something. A new kind of build is either
/// defined in the "Build modes" bullet or, if it is no kind of build, added here.
const NOT_MODES: &[&str] = &[
    // Determiners, numbers and pronouns: "the build", "each build", "the program's build".
    "a",
    "the",
    "each",
    "every",
    "any",
    "per",
    "no",
    "one",
    "two",
    "three",
    "other",
    "first",
    "next",
    "its",
    "whose",
    "which",
    "that",
    "them",
    "it",
    "you",
    "s",
    "t",
    "5", //
    // "build" as a verb: "to build", "can build", "also build", "does not build".
    "to",
    "can",
    "will",
    "also",
    "never",
    "not",
    "then",
    "and",
    "are",
    "at",
    "yields",
    "above",
    "across",
    "between", //
    // Subjects of the verb "builds": "the step builds", "the stage builds".
    "step",
    "stage",
    "row",
    "library",
    "program",
    "plan",
    "pattern",
    "tier",
    "body",
    "design",
    "elaboration",
    "equality",
    "integers",
    "primes",
    "runtime",
    "source",
    "compiler",
    "checker",
    "itself",
    "number",
    "doubling",
    "sqlite",
    "arduino",
    "access",
    "alternative",
    "2-forms",
    "zed",
    "main",
    "search",
    "which", //
    // A build of a program, a command or a toolchain, and not a kind of build: a corpus
    // program's build, the native engine's beside the interpreter, the class of the test builds
    // the bullet lists, a pinned toolchain's, builds that are reproducible, the CLI command.
    "corpus",
    "native",
    "test",
    "toolchain",
    "reproducible",
    "cross",
    "total",
    "zedc", //
    // The executable's "GNU build ID" (step L1.36b), an ELF note, not a kind of build.
    "gnu",
];

/// Whether `word` names a layer or a step of the plan, as in "L4 builds groups" or "step L1.24
/// builds the lattice", in the forms of Part G: a layer `l` or `m` with its digits, alone or
/// followed by a `.` and the step's number with any suffix (`l1.36b`, `l10.4d`,
/// `l1.29d-package`), or row `s` followed by a step's number (`s.5`, `s.2-forms`).
fn is_step(word: &str) -> bool {
    let (layer, step) = word
        .split_once('.')
        .map_or((word, None), |(l, s)| (l, Some(s)));
    let numbered = step.is_some_and(|s| s.starts_with(|c: char| c.is_ascii_digit()));
    match layer.strip_prefix(['l', 'm']) {
        Some(n) if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) => {
            step.is_none() || numbered
        }
        _ => layer == "s" && numbered,
    }
}

/// The "Build modes" bullet of `design`, from its first line to the next bullet.
fn bullet(design: &str) -> Result<&str, String> {
    const HEAD: &str = "\n- **Build modes.**";
    let start = design
        .find(HEAD)
        .ok_or("DESIGN.md has no bullet \"Build modes\"")?
        + 1;
    let end = design[start + HEAD.len()..]
        .find("\n- **")
        .map_or(design.len(), |i| start + HEAD.len() + i);
    Ok(&design[start..end])
}

/// Each place in `text` where a word stands before "build" or "builds": its 1-based line and
/// the word, lowercased. A word is letters, digits and `-`, with a `.` that has such a byte on
/// each side, so a step id such as `L1.24` is one word and a sentence's last `.` is not part of
/// one. One pass over the text; each byte is read back at most once more, as part of the word
/// before the "build" that follows it.
pub fn before_build(text: &str) -> Vec<(usize, String)> {
    let bytes = text.as_bytes();
    let word_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'-';
    let mut out = Vec::new();
    let (mut line, mut counted) = (1, 0);
    for (at, _) in text.match_indices("build") {
        let mut after = at + "build".len();
        if bytes.get(after) == Some(&b's') {
            after += 1;
        }
        if bytes.get(after).is_some_and(|&b| word_byte(b)) || at == 0 || bytes[at - 1] != b' ' {
            continue;
        }
        let end = at - 1;
        let mut start = end;
        while start > 0
            && (word_byte(bytes[start - 1])
                || bytes[start - 1] == b'.'
                    && start < end
                    && start >= 2
                    && word_byte(bytes[start - 2]))
        {
            start -= 1;
        }
        if start == end {
            continue;
        }
        line += bytes[counted..at].iter().filter(|&&b| b == b'\n').count();
        counted = at;
        out.push((line, text[start..end].to_ascii_lowercase()));
    }
    out
}

/// The kinds of build the bullet defines: the words before each italic "… build*".
fn defined(bullet: &str) -> Vec<String> {
    let mut names: Vec<String> = bullet
        .match_indices(" build*")
        .filter_map(|(at, _)| {
            let start = bullet[..at].rfind(['*', ' '])? + 1;
            Some(bullet[start..at].to_ascii_lowercase())
        })
        .collect();
    zed_collections::sorted::sort_dedup(&mut names);
    names
}

/// The cells of the table row of `bullet` whose first cell is `first`.
fn row<'a>(bullet: &'a str, first: &str) -> Result<Vec<&'a str>, String> {
    let line = bullet
        .lines()
        .find(|l| l.starts_with('|') && l[1..].trim_start().starts_with(first))
        .ok_or_else(|| format!("the build modes table has no row \"{first}\""))?;
    Ok(crate::table::cells(line))
}

/// The places in `design` outside the bullet where a word names a kind of build that the
/// bullet does not define, each as `line: "word build"`.
pub fn undefined_builds(design: &str) -> Result<Vec<String>, String> {
    let b = bullet(design)?;
    let names = defined(b);
    let start = b.as_ptr() as usize - design.as_ptr() as usize;
    let line = |at: usize| zedc::source::line_col(design.as_bytes(), at).0;
    let (first, last) = (line(start), line(start + b.len()));
    Ok(before_build(design)
        .into_iter()
        .filter(|(line, word)| {
            !(first..=last).contains(line)
                && !names.contains(word)
                && !NOT_MODES.contains(&word.as_str())
                && !is_step(word)
        })
        .map(|(line, word)| format!("{line}: \"{word} build\""))
        .collect())
}

/// The kinds of build the bullet must define (plan row BUILD-modes).
const MODES: &[&str] = &[
    "as-observed",
    "checked",
    "counting",
    "debug",
    "default",
    "full",
    "guard-page",
    "optimized",
    "precise",
    "strict",
];

/// Whether the "Build modes" bullet of `design` has the table of the debug build and the
/// optimized build, each keeping the program's values, and defines `MODES`, and every kind of
/// build `design` names elsewhere is one it defines. The first difference otherwise.
pub fn build_modes(design: &str) -> Result<(), String> {
    let b = bullet(design)?;
    let head = row(b, "|")?;
    if head != ["", "Debug build", "Optimized build"] {
        return Err(format!("the build modes table's columns are {head:?}"));
    }
    let values = row(b, "Values")?;
    if values.len() != 3
        || !values[1].contains("definitional interpreter")
        || values[2] != "the same"
    {
        return Err(format!("the build modes table's row Values is {values:?}"));
    }
    for first in ["Log mode", "Log units", "Checks", "Optimization"] {
        let cells = row(b, first)?.len();
        if cells != 3 {
            return Err(format!(
                "the build modes table's row {first} has {cells} cells"
            ));
        }
    }
    let defined = defined(b);
    if defined != MODES {
        return Err(format!(
            "the bullet defines the builds {defined:?}, not {MODES:?}"
        ));
    }
    let undefined = undefined_builds(design)?;
    if !undefined.is_empty() {
        return Err(format!(
            "DESIGN.md names builds the bullet does not define: {undefined:?}"
        ));
    }
    Ok(())
}

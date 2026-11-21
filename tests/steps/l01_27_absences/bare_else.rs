//! An `else` names every atom it takes (DESIGN.md sec:failure, QUESTIONS A113, plan row
//! ELSE-explicit-atoms): a bare `e else d`, and a name alone after `else`, `e else err -> d`, are
//! refused with the row "An `else` that does not name its atoms" of sec:diagnostics. The repair
//! lists exactly the loose atoms of `e`'s type, in the order of the printed type, as the chain
//! `e else #a -> d else #b -> d` (zedc is before L2, whose union `e else (#a | #b) -> d` is plan
//! row OR-PAT-check); family atoms are data and never listed; an `e` with no loose atom gets the
//! menu of an `else` with nothing to take (QUESTIONS A67).

use std::path::{Path, PathBuf};

use zed_kernel::types::Type as KType;
use zedc::check::ty::{Carrier, Ty};
use zedc::lex::{Part, Tok, Token};

use zed_tests::step_helpers::l01_19_whole_file_ports::{run, zedc};
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, menu, type_errors};

/// A lookup that misses: a number, or the loose failure `#notFound`.
const LOOKUP: &str = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";

#[test]
fn a_bare_else_is_refused_with_its_span_and_the_chain_of_its_loose_atoms() {
    // Three loose atoms, written in another order than the printed type's: the chain follows
    // the printed type, `#empty`, `#none`, `#notFound`.
    let t = "f(positional x: int | #notFound | #none | #empty) = x else 0;\n";
    assert_eq!(
        type_errors(t),
        [
            "`x else 0` does not name the atoms it takes. Try `x else #empty -> 0 else #none -> 0 \
          else #notFound -> 0` instead.\n  fixes, each checked here:\n    f(positional x: int | \
          #notFound | #none | #empty) = x else #empty -> 0 else #none -> 0 else #notFound -> 0;    \
          the `else` takes #empty, #none, #notFound [x else 0]"
        ]
    );
    // The span runs from the operand to the default, and stays inside parentheses around the
    // `else`, so the chain the repair appends stays inside them too.
    let p = format!("{LOOKUP}f(positional k: int) = (lookup(k) else -1) + 1;\n");
    assert_eq!(
        type_errors(&p),
        [
            "`lookup(k) else -1` does not name the atoms it takes. Try `lookup(k) else #notFound \
          -> -1` instead.\n  fixes, each checked here:\n    f(positional k: int) = (lookup(k) \
          else #notFound -> -1) + 1;    the `else` takes #notFound [lookup(k) else -1]"
        ]
    );
}

/// The program `src` after each refusal `zedc run` prints for it is repaired by its first fix,
/// in turn, until it loads: the refused line, found by the `file:line:col` the refusal starts
/// with, replaced by the first line under "fixes, each checked here:", with the refused line's
/// indentation. Panics when a refusal has no fix, or after more rounds than `src` has lines.
fn repaired(name: &str, src: &str) -> (String, String) {
    let mut src = src.to_string();
    for _ in 0..=src.lines().count() {
        let out = run(name, &src, "", &[]);
        if out.status == 0 {
            return (src, out.stdout);
        }
        let first = out.stderr.lines().next().unwrap();
        assert!(
            first.contains("does not name the atoms it takes"),
            "{}",
            out.stderr
        );
        let line: usize = first
            .split(".zed:")
            .nth(1)
            .unwrap()
            .split(':')
            .next()
            .unwrap()
            .parse()
            .unwrap();
        let fix = (out.stderr.lines())
            .skip_while(|l| *l != "  fixes, each checked here:")
            .nth(1)
            .unwrap_or_else(|| panic!("a fix: {}", out.stderr));
        let fix = fix.trim_start().rsplit_once("    ").unwrap().0.trim_end();
        let mut lines: Vec<String> = src.lines().map(str::to_string).collect();
        let old = &lines[line - 1];
        let indent = &old[..old.len() - old.trim_start().len()];
        lines[line - 1] = format!("{indent}{fix}");
        src = lines.join("\n") + "\n";
    }
    panic!("{name}: still refused after every round:\n{src}");
}

#[test]
fn each_repair_builds_and_keeps_the_output_the_bare_else_meant() {
    // Each program, the output its bare `else`s gave when a bare `else` defaulted every loose
    // atom (before QUESTIONS A113), and the program the repairs give.
    let cases = [
        (
            "two_atoms",
            "f(positional x: int | #notFound | #none) = x else 0;\nmain(m: MainArgs) {\n    \
             m.stdout <- \"${f(#none)} ${f(#notFound)} ${f(4)}\";\n}\n",
            "0 0 4\n",
            "f(positional x: int | #notFound | #none) = x else #none -> 0 else #notFound -> 0;\n",
        ),
        (
            "atom_default",
            "lookup(positional k: int) = if k > 0 { k } else { #notFound };\nmain(m: MainArgs) \
             {\n    _ = lookup(3) else #ok;\n    m.stdout <- \"${lookup(-1) else 7}\";\n}\n",
            "7\n",
            "    _ = lookup(3) else #notFound -> #ok;\n    m.stdout <- \"${lookup(-1) else \
             #notFound -> 7}\";\n",
        ),
        (
            "command_line",
            "main(m: MainArgs) {\n    m.stdout <- m.args[0] else \"none\";\n}\n",
            "none\n",
            "    m.stdout <- m.args[0] else #outOfBounds -> \"none\";\n",
        ),
        (
            "float_division",
            "f(positional c: f64, positional z: f64) = c / z else 0.0;\nmain(m: MainArgs) {\n    \
             m.stdout <- \"${f(1.0, 2.0)}\";\n}\n",
            "0.5\n",
            "f(positional c: f64, positional z: f64) = c / z;\n",
        ),
    ];
    for (name, bare, output, lines) in cases {
        let refused = run(&format!("{name}_bare"), bare, "", &[]);
        assert_eq!(refused.status, 1, "{name}: {}", refused.stderr);
        let (fixed, out) = repaired(name, bare);
        assert_eq!(out, output, "{name}:\n{fixed}");
        assert!(fixed.contains(lines), "{name}:\n{fixed}");
    }
}

#[test]
fn a_name_alone_after_else_gets_the_same_headline() {
    // The parser refuses it, having no types, so its repair says in words what the checker's
    // repair of a bare `else` writes out.
    let out = run(
        "binder",
        "f(positional x: int | #notFound) = x else err -> 0;\nmain(m: MainArgs) {\n    m.stdout \
         <- \"${f(4)}\";\n}\n",
        "",
        &[],
    );
    assert_eq!(out.status, 1);
    let lines: Vec<&str> = out.stderr.lines().collect();
    assert!(
        lines[0].ends_with(".zed:1:36: `x else err -> 0` does not name the atoms it takes."),
        "{}",
        out.stderr
    );
    assert!(
        out.stderr.contains(
            "repair: name each atom the `else` takes in place of `err`, `else #a -> 0` for an \
             atom `#a`; a name binds only inside an atom's payload, `else #a(err) -> 0`"
        ),
        "{}",
        out.stderr
    );
}

#[test]
fn an_operand_with_no_loose_atom_gets_the_menu_of_an_else_with_nothing_to_take() {
    let int = "f(positional x: int) = x else 0;\n";
    assert_eq!(
        type_errors(int),
        [
            "`x else 0` does not name the atoms it takes. Try `x` instead.\n  fixes, each checked \
          here:\n    f(positional x: int) = x;    the `else` is gone; the value is `x` [x else 0]"
        ]
    );
    // A float division gives NaN or infinity, not an atom: the second fix tests the divisor.
    let float = "f(positional c: f64, positional z: f64) = c / z else 0.0;\n";
    let fixes = menu(&[
        (
            "f(positional c: f64, positional z: f64) = c / z;",
            "the `else` is gone; the value is `c / z`",
        ),
        (
            "f(positional c: f64, positional z: f64) = if z == 0 { 0.0 } else { c / z };",
            "0.0 where z is 0",
        ),
    ]);
    assert_eq!(
        type_errors(float),
        [format!(
            "`c / z else 0.0` does not name the atoms it takes. Try `c / z` instead.{fixes} \
             [c / z else 0.0]"
        )]
    );
}

/// `#a | #b | …`.
fn atoms(names: &[&str]) -> Ty {
    (names.iter()).fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
}

/// The errors of `text` with the name its first statement binds given the type `v`, as a `type`
/// declaration will give it (step L2.5): each message, then its notes, one line each.
fn errors_given(text: &str, v: &Ty) -> Vec<String> {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    (zedc::check::walk::check_given(&stmts, &res, text, v.clone())
        .errors
        .into_iter())
    .map(|e| {
        let notes = e.notes.iter().map(|n| format!("\n{}", n.text));
        format!("{}{}", e.message, notes.collect::<String>())
    })
    .collect()
}

#[test]
fn the_repair_never_lists_a_family_atom() {
    // `Color | #ioError`: the family's atoms are data, and only the loose `#ioError` is listed.
    let color = atoms(&["red", "green", "blue"]).named();
    let text = "v = 0;\ny = v else 5;\n";
    let e = errors_given(text, &color.union(&atoms(&["ioError"])));
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(
        e[0].starts_with(
            "`v else 5` does not name the atoms it takes. Try `v else #ioError -> 5` instead."
        ),
        "{e:?}"
    );
    // A family alone holds no loose atom: the menu of an `else` with nothing to take.
    let e = errors_given(text, &color.union(&Ty::carrier(Carrier::Int)));
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(
        e[0].starts_with("`v else 5` does not name the atoms it takes. Try `v` instead."),
        "{e:?}"
    );
    assert!(
        e[0].contains("which holds no loose atom, so the `else` never takes one"),
        "{e:?}"
    );
    // Written without the family's name, every atom is loose, and the chain lists all four in
    // the order of the printed type.
    let e = errors_given(text, &color.union(&atoms(&["ioError"])).written());
    assert!(
        e[0].starts_with(
            "`v else 5` does not name the atoms it takes. Try `v else #blue -> 5 else #green -> 5 \
             else #ioError -> 5 else #red -> 5` instead."
        ),
        "{e:?}"
    );
}

#[test]
fn a_bare_else_after_a_call_into_another_unit() {
    // zedc does not yet link a use to another unit's definition (step L2.4, which resolves unit
    // names), so a bare `else` after such a call never loads: the package is refused at the
    // call. The same call to a definition in the file is refused at the `else`, its repair naming
    // the callee's loose atom. Plan row ELSE-cross-unit holds the test once L2.4 links the call:
    // the same headline and repair as here.
    let call = "main(m: MainArgs) {\n    m.stdout <- \"${lib.lookup(3) else 0}\";\n}\n";
    let d = zed_tests::step_helpers::scratch_dir("l01_27_bare_else/package");
    for (file, text) in [
        ("zed.manifest", String::new()),
        ("lib.zed", LOOKUP.to_string()),
        ("main.zed", format!("import lib;\n{call}")),
    ] {
        std::fs::write(d.join(file), text).unwrap();
    }
    let main = d.join("main.zed");
    let out = zedc(&["run", main.to_str().unwrap()], "");
    assert_eq!(out.status, 1, "{}", out.stderr);
    assert!(
        out.stderr.contains(
            "`lib.lookup`, a definition of another unit, is used here, and this version of zedc \
             does not yet link a use to a definition in another unit."
        ),
        "{}",
        out.stderr
    );
    let local = format!("{LOOKUP}{}", call.replace("lib.lookup", "lookup"));
    let out = run("bare_else_local_call", &local, "", &[]);
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains(
            "`lookup(3) else 0` does not name the atoms it takes. Try `lookup(3) else #notFound \
             -> 0` instead."
        ),
        "{}",
        out.stderr
    );
}

/// The tokens of `tokens`, those in each string's holes included, in text order.
fn flat<'t>(tokens: &'t [Token], out: &mut Vec<&'t Tok>) {
    for t in tokens {
        out.push(&t.tok);
        if let Tok::Str(parts) = &t.tok {
            for p in parts {
                if let Part::Hole { tokens, .. } = p {
                    flat(tokens, out);
                }
            }
        }
    }
}

/// The index of the token after the bracket that closes the `(` at `i` of `toks`, if any.
fn past_parens(toks: &[&Tok], i: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (j, t) in toks.iter().enumerate().skip(i) {
        match t {
            Tok::Op("(") => depth += 1,
            Tok::Op(")") => {
                depth -= 1;
                if depth == 0 {
                    return Some(j + 1);
                }
            }
            _ => {}
        }
    }
    None
}

/// How many `else`s of `text` name no atom, read from the lexer's tokens so that comments and
/// the text of strings are skipped and the code in a string's holes is read. An `else` names
/// its atoms where `{` or `if` follows it (the `else` of an `if`), or an atom pattern and `->`:
/// an atom, with or without a parenthesized payload pattern (`#e(code:)`), or a parenthesized
/// union of them (`(#a | #b)`). So `x else #ok`, an atom default with no `->`, is bare.
/// Linear in the tokens but for the payload scans, each over the brackets after one `else`.
fn bare_elses(text: &str) -> Result<usize, String> {
    let tokens = zedc::lex::lex_fence(text).map_err(|e| format!("{e:?}"))?;
    let mut toks = Vec::new();
    flat(&tokens, &mut toks);
    let arrow = |i: Option<usize>| i.is_some_and(|i| toks.get(i) == Some(&&Tok::Op("->")));
    let named = |i: usize| match toks.get(i) {
        Some(Tok::Op("{")) | Some(Tok::Keyword("if")) => true,
        Some(Tok::Atom(_)) => match toks.get(i + 1) {
            Some(Tok::Op("(")) => arrow(past_parens(&toks, i + 1)),
            _ => arrow(Some(i + 1)),
        },
        Some(Tok::Op("(")) => {
            matches!(toks.get(i + 1), Some(Tok::Atom(_))) && arrow(past_parens(&toks, i))
        }
        _ => false,
    };
    Ok((0..toks.len())
        .filter(|&i| *toks[i] == Tok::Keyword("else") && !named(i + 1))
        .count())
}

/// Each `.zed` file under `dir`, at any depth.
fn zed_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            zed_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "zed") {
            out.push(p);
        }
    }
}

#[test]
fn no_program_of_the_repository_has_a_bare_else() {
    // The corpus, the fence fixtures, the prelude and every other `.zed` file under `zed/`, and
    // the fences of README.md. libzed (/home/luke/Work/libzed, a repository of its own that no
    // test here reads) held no program on 2026-11-21. A file the lexer refuses is a failure.
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    zed_files(&root.join("zed"), &mut files);
    files.sort();
    let mut found = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).unwrap();
        match bare_elses(&text) {
            Ok(0) => {}
            n => found.push(format!("{}: {n:?}", f.display())),
        }
    }
    for f in zed_tests::fences::readme() {
        match bare_elses(&f.text) {
            Ok(0) => {}
            n => found.push(format!("{}: {n:?}", f.at)),
        }
    }
    assert!(files.len() > 100, "{}", files.len());
    assert_eq!(found, Vec::<String>::new());
    // The scan finds each bare form, and none of the named ones.
    let bare = "a = x else 0;\nb = \"${x else 1}\";\nc = x else err -> 0;\nd = x else #ok;\n";
    let named = "a = x else #e -> 0;\nb = x else (#e | #f) -> 0;\nc = if x { 1 } else { 2 };\n\
                 d = if x { 1 } else if y { 2 } else { 3 }; // x else 0\ne = \"x else 0\";\n";
    assert_eq!(bare_elses(bare), Ok(4));
    assert_eq!(bare_elses(named), Ok(0));
}

/// `lookup` and `n` bindings `a<i> = lookup(i) else 0;`, each a bare `else`.
pub(super) fn bare_else_units(n: usize) -> String {
    let mut t = String::from(LOOKUP);
    for i in 0..n {
        t.push_str(&format!("a{i} = lookup({i}) else 0;\n"));
    }
    t
}

/// The check refuses each of the `n` bare `else`s of `u` once, each with its repair.
pub(super) fn each_bare_else_refused_once(u: &Resolved, n: usize) {
    let e = u.check().errors;
    assert_eq!(e.len(), n);
    assert!(e.iter().all(|e| e.message.contains("Try `lookup(")));
}

#[test]
fn each_bare_else_is_refused_once() {
    for n in [1, 3] {
        each_bare_else_refused_once(&Resolved::new(&bare_else_units(n)), n);
    }
}

/// `f(positional x: int | #a0 | … | #a(n-1)) = x else 0;`, one bare `else` over n loose atoms.
pub(super) fn many_atoms(n: usize) -> String {
    let atoms: String = (0..n).map(|i| format!(" | #a{i}")).collect();
    format!("f(positional x: int{atoms}) = x else 0;\n")
}

/// The one error of `u`, [`many_atoms`]`(n)`, whose repair names each of the n atoms once.
pub(super) fn lists_each_atom_once(u: &Resolved, n: usize) {
    let e = u.check().errors;
    assert_eq!(e.len(), 1);
    assert_eq!(e[0].menu.matches(" -> 0").count(), n);
    assert!(e[0].menu.contains(&format!(" else #a{} -> 0", n - 1)));
}

#[test]
fn the_repair_lists_each_of_many_atoms_once() {
    for n in [1, 4] {
        lists_each_atom_once(&Resolved::new(&many_atoms(n)), n);
    }
}

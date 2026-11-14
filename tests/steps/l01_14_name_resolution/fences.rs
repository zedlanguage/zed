use super::{run, run_stmts};
use zedc::ast::{Stmt, StmtKind, unit};
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The programs of a fence's statements `stmts`. A fence may set several whole programs side by
/// side, each with its own `main`, as DESIGN sec:checking_in_zed does for two rejected programs
/// and an accepted one; read as one unit, the second `main` would be a second declaration. So a
/// fence with more than one `main` holds one program per `main`: the statements after the
/// previous `main` up to its own, the statements after the last `main` joining the last
/// program. A fence with one `main` or none is one program.
///
/// Complexity tradeoff: one pass over the statements, O(s) for s statements, and each program a
/// slice of `stmts`, so no statement is copied or read twice. The other reading the plan row
/// named, a mark in the document that a fence holds several programs, needs the spec to carry
/// the mark; the `main`s already say it.
fn programs(stmts: &[Stmt]) -> Vec<&[Stmt]> {
    let is_main = |s: &Stmt| matches!(&s.bare().kind, StmtKind::Function(f) if f.main.is_some());
    // The end of each program: just after its `main`, and for the last, the end of the fence.
    let mut ends: Vec<usize> = (1..=stmts.len())
        .filter(|&i| is_main(&stmts[i - 1]))
        .collect();
    match ends.last_mut() {
        Some(last) => *last = stmts.len(),
        None => return vec![stmts],
    }
    let mut start = 0;
    ends.into_iter()
        .map(|end| {
            let program = &stmts[start..end];
            start = end;
            program
        })
        .collect()
}

/// Every documentation unit that builds resolves, or fails only on what a fragment leaves to
/// the text around it: a name or type it does not bind, or a rebinding the fence marks ✗; or
/// on a form of layer L2, L3, L5 or L6 that the parser builds and a later step compiles, or an
/// annotation, prelude word or prelude type of a later layer; or on an import, which a fragment read alone,
/// with no package around it, cannot follow. A fence of several programs is resolved one
/// program at a time ([`programs`]).
#[test]
fn every_building_fence_resolves_but_for_its_free_names() {
    let (mut resolved, mut built) = (0, 0);
    for f in zed_tests::fences::all().iter().filter(|f| !f.notation) {
        let tokens = lex_fence(&f.text).unwrap();
        let tree = parse(&f.text, &tokens, "Unit", TOP).unwrap();
        let Ok(stmts) = unit(&f.text, &tokens, &tree) else {
            continue;
        };
        for program in programs(&stmts) {
            built += 1;
            match run_stmts(&f.text, program) {
                Ok(_) => resolved += 1,
                Err(es) => {
                    for e in es {
                        let free = e.contains(" is not defined.");
                        let marked = e.contains("already bound") && f.text.contains('✗');
                        let later = zed_tests::is_not_yet(&e);
                        // A fragment read alone has no package around it, so it imports no unit.
                        let alone = e.contains("cannot be imported: no manifest");
                        assert!(free || marked || later || alone, "{}: {e}", f.at);
                    }
                }
            }
        }
    }
    assert!(
        built >= 23 && resolved >= 2,
        "{built} built, {resolved} resolved"
    );
}

/// The statements of `text`, built as a unit.
fn stmts(text: &str) -> Vec<Stmt> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    unit(text, &tokens, &tree).unwrap()
}

/// The text of each program of `text`, from its first statement to its last.
fn program_texts(text: &str) -> Vec<String> {
    programs(&stmts(text))
        .iter()
        .map(|p| text[p[0].span.start..p[p.len() - 1].span.end].to_string())
        .collect()
}

#[test]
fn a_fence_of_three_programs_resolves_each_on_its_own() {
    // The form of DESIGN sec:checking_in_zed: two programs of `main` alone, then one whose
    // `main` calls a function written before it.
    let text = "main(m: MainArgs) {\n  m.stdout <- \"one\";\n}\n\
                main(m: MainArgs) {\n  k = int(m.args[0] else \"\") else 0;\n  m.stdout <- String(k);\n}\n\
                grow(k: int) {\n  return k + 1;\n}\n\
                main(m: MainArgs) {\n  m.stdout <- String(grow(k: 2));\n}\n";
    let e = run(text).unwrap_err();
    assert!(
        e[0].starts_with("`main` is already declared in this scope with these parameter types"),
        "{e:?}"
    );
    let all = stmts(text);
    let ps = programs(&all);
    assert_eq!(ps.iter().map(|p| p.len()).collect::<Vec<_>>(), [1, 1, 2]);
    for p in ps {
        assert!(run_stmts(text, p).is_ok());
    }
}

#[test]
fn statements_after_the_last_main_join_the_last_program() {
    assert_eq!(
        program_texts(
            "a = 1;\nmain(m: MainArgs) { m.stdout <- String(a); }\nb = 2;\nmain(m: MainArgs) { m.stdout <- String(c); }\nc = 3;\nd = 4;\n"
        ),
        [
            "a = 1;\nmain(m: MainArgs) { m.stdout <- String(a); }",
            "b = 2;\nmain(m: MainArgs) { m.stdout <- String(c); }\nc = 3;\nd = 4;",
        ]
    );
}

#[test]
fn a_fence_with_one_main_or_none_is_one_program() {
    let one = "f(x: int) = x;\nmain(m: MainArgs) { m.stdout <- String(f(x: 1)); }\ng = 2;\n";
    assert_eq!(program_texts(one), [one.trim_end()]);
    let none = "f(x: int) = x;\ng = f(x: 2);\n";
    assert_eq!(program_texts(none), [none.trim_end()]);
    // An annotated `main` is a `main`.
    assert_eq!(
        program_texts("@timeout(10)\nmain(m: MainArgs) { m.stdout <- \"a\"; }\nmain(m: MainArgs) { m.stdout <- \"b\"; }\n").len(),
        2
    );
    // No statements: one empty program.
    assert_eq!(programs(&[]).len(), 1);
}

/// A fence of `k` programs, each a function and a `main` that calls it, and its statements,
/// for the benchmark of `bench/fences.rs`.
pub(super) fn fence_of(k: usize) -> (String, Vec<Stmt>) {
    let text = (0..k)
        .map(|i| format!("step{i}(x: int) = x;\nmain(m: MainArgs) {{ m.stdout <- String(step{i}(x: {i})); }}\n"))
        .collect::<String>();
    let s = stmts(&text);
    (text, s)
}

/// Splits `s`, the statements of the fence `text` of `k` programs, into its programs and checks
/// that there are `k` and that each resolves on its own.
pub(super) fn each_program_resolves(text: &str, s: &[Stmt], k: usize) {
    let ps = programs(s);
    assert_eq!(ps.len(), k);
    for p in ps {
        assert!(run_stmts(text, p).is_ok());
    }
}

/// A fence of a few programs, each a function and its `main`, splits into its programs and
/// each resolves; `bench/fences.rs` holds the timing.
#[test]
fn a_fence_of_a_few_programs_resolves_each_on_its_own() {
    for k in [1, 2, 9] {
        let (text, s) = fence_of(k);
        each_program_resolves(&text, &s, k);
    }
}

#[test]
fn the_corpus_program_that_builds_resolves() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../zed/corpus/09-canonical-equal.zed"
    );
    let text = std::fs::read_to_string(path).unwrap();
    assert!(run(&text).is_ok());
}

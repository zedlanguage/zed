//! Moving definitions (FAIL-queries-reorder, found by TEST-complete-diagnostics): DESIGN.md
//! step L1.30 keys the queries by content, so a row whose definitions and case keep their text
//! is reused wherever they move, as a comment above them already reuses every row
//! (reuse.rs, `a_comment_reruns_the_front_end_and_no_row`). A row's key held the numbers
//! elaboration gives binders across the whole unit (`n@2`, `$7`) and listed the definitions in
//! the unit's order; it now holds neither (`Db::cone`). A key still changes with what can change
//! a row's answer: a definition's text, and the name a binder is written with, which a result
//! can print.

use zedc::query::{Db, Query};

use super::{PRICING, checks};

/// The rows and waves computed so far.
fn rows(db: &Db) -> [usize; 2] {
    [Query::Row, Query::Wave].map(|q| db.computed(q))
}

/// `b` checked under `db` after `a`: the answers, which must be a fresh database's, and the
/// rows and waves computed for `b` alone.
fn after(a: &str, b: &str) -> (Vec<String>, [usize; 2]) {
    let mut db = Db::new();
    checks(&mut db, a);
    let [r, w] = rows(&db);
    let got = checks(&mut db, b);
    assert_eq!(
        got,
        checks(&mut Db::new(), b),
        "the answers of a fresh database"
    );
    let [r2, w2] = rows(&db);
    (got, [r2 - r, w2 - w])
}

/// `a` and `b`, two units of two parts, with the parts swapped in `b`.
fn swapped(first: &str, second: &str) -> (String, String) {
    (format!("{first}\n{second}"), format!("{second}\n{first}"))
}

/// DESIGN.md L1.30: the queries are keyed by content hashes. Moving whole definitions with
/// their tables changes no definition's text and no case's text, so every row is reused, as a
/// comment above them already reuses every row (reuse.rs, `a_comment_reruns_the_front_end_and_no_row`).
#[test]
fn reordered_definitions_reuse_every_row() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let rows = db.computed(Query::Row);
    // `tax` and its table moved above `discount`: the texts are the same.
    let mut parts: Vec<&str> = PRICING.split("\n\n").collect();
    parts.swap(0, 1);
    let moved = parts.join("\n\n");
    let got = checks(&mut db, &moved);
    assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    assert_eq!(db.computed(Query::Row), rows);
}

/// The smallest case: two functions that read nothing of each other, one row each.
#[test]
fn two_independent_tables_swapped_reuse_both_rows() {
    let a = "f(positional n: int) = n + 1\ntest { 1 -> 2 }\n\ng(positional n: int) = n + 2\ntest { 1 -> 3 }\n";
    let b = "g(positional n: int) = n + 2\ntest { 1 -> 3 }\n\nf(positional n: int) = n + 1\ntest { 1 -> 2 }\n";
    let mut db = Db::new();
    checks(&mut db, a);
    assert_eq!(db.computed(Query::Row), 2);
    checks(&mut db, b);
    assert_eq!(db.computed(Query::Row), 2);
}

/// A definition whose written name another binder has is numbered by its place among them
/// (`n@1` or `n@2`); moved, its row and the row that reads it are reused.
#[test]
fn a_definition_named_as_a_parameter_elsewhere_moves_with_its_rows() {
    let (a, b) = swapped(
        "n(positional k: int) = k + 1\ntest { 1 -> 2 }\n",
        "g(positional n: int) = n + 2\ntest { 1 -> 3 }\n\nh(positional k: int) = n(k) * 2\ntest { 1 -> 4 }\n",
    );
    let (got, computed) = after(&a, &b);
    assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    assert_eq!(computed, [0, 0]);
}

/// Temporaries, numbered across the whole unit (`$k`), move with their definitions.
#[test]
fn definitions_with_temporaries_move_with_their_rows() {
    let (a, b) = swapped(
        "f(positional n: int) = { y, z = (n, 1); y + z }\ntest { 1 -> 2 }\n",
        "g(positional n: int) = { y, z = (n, 2); y + z }\ntest { 1 -> 3 }\n",
    );
    let (got, computed) = after(&a, &b);
    assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    assert_eq!(computed, [0, 0]);
}

/// A row that reads two definitions is reused when the two trade places.
#[test]
fn a_row_reading_two_definitions_that_trade_places_is_reused() {
    let tail = "both(positional n: int) = f(n) + g(n)\ntest { 1 -> 5 }\n";
    let (a, b) = swapped(
        "f(positional n: int) = n + 1;\n",
        "g(positional n: int) = n + 2;\n",
    );
    let (got, computed) = after(&format!("{a}\n{tail}"), &format!("{b}\n{tail}"));
    assert_eq!(got, ["6:8: ok"]);
    assert_eq!(computed, [0, 0]);
}

/// A changed text still runs its rows again, wherever it moves: a body, and a moved
/// definition whose body changed with the move.
#[test]
fn a_changed_definition_runs_its_rows_again_where_it_moves() {
    let (a, _) = swapped(
        "f(positional n: int) = n + 1\ntest { 1 -> 2 }\n",
        "g(positional n: int) = n + 2\ntest { 1 -> 3 }\n",
    );
    let b = "g(positional n: int) = n + 2\ntest { 1 -> 3 }\n\nf(positional n: int) = n + 2\ntest { 1 -> 2 }\n";
    let (got, computed) = after(&a, b);
    assert_eq!(got, ["2:8: ok", "5:8: `1 -> 2` of `f`: the result is 3"]);
    assert_eq!(computed, [1, 0]);
}

/// A parameter written with another name runs the row again: a result can name it.
#[test]
fn a_renamed_parameter_runs_the_row_again() {
    let a = "f(positional n: int) = n + 1\ntest { 1 -> 2 }\n";
    let b = "f(positional m: int) = m + 1\ntest { 1 -> 2 }\n";
    let (got, computed) = after(a, b);
    assert_eq!(got, ["2:8: ok"]);
    assert_eq!(computed, [1, 0]);
}

/// A row of `main`'s table names `main`'s parameter as it is written, so a wave whose `main`
/// renames it runs again and names the new one; a function moved above `main` reuses it.
#[test]
fn a_wave_is_reused_when_moved_and_names_mains_parameter_as_written() {
    let shout = "shout(positional s: String) = upper(s) ++ \"!!\";\n";
    let main = "main(m: MainArgs) {\n  m.stdout <- shout(m.stdin[0] else \"\");\n}\n\
                test { \"hi\" -> \"HI!\\n\" }\n";
    let first = format!("{shout}{main}");
    let wrong = "`\"hi\" -> \"HI!\\n\"` of `main`: `m.stdout` writes \"HI!!\\n\"";
    let (got, computed) = after(&first, &format!("{main}{shout}"));
    assert_eq!(got, [format!("4:8: {wrong}")]);
    assert_eq!(computed, [0, 0]);
    let renamed = first.replace("m.", "a.").replace("(m:", "(a:");
    let (got, computed) = after(&first, &renamed);
    assert_eq!(got, [format!("5:8: {}", wrong.replace("m.", "a."))]);
    assert_eq!(computed, [0, 1]);
}

//! Printed types do not move (step L1.29a, DESIGN.md sec:diagnostics). The types a unit's
//! check prints, in its messages and as the signature of each top-level name, are the same
//! text when the unit is checked again, alone on a fresh thread or after every other unit,
//! with its items in another order, and with a line added that no printed type depends on: a
//! comment, or an unrelated binding. A type name taken from a fresh counter or a source
//! position would differ between these.

use std::collections::BTreeMap;

use zed_tests::scaling;
use zedc::check::ty::printed;

use super::order::{items, units};
use super::printed::unsolved;

/// The types the check of a unit prints.
#[derive(PartialEq, Eq, Debug, Clone)]
struct Shown {
    /// Each type printed in its messages, in the order printed. A text that holds a class of
    /// the solver, `$k`, is left out: it is a placeholder the checker replaces once the class
    /// is solved, and no message shows it (printed.rs).
    said: Vec<String>,
    /// The type of each top-level name bound by `=`, and the signatures of each function, in
    /// any scope, by name; a name declared more than once has its signatures sorted.
    tops: BTreeMap<String, Vec<String>>,
}

/// The types printed by the check of `text`.
fn shown(text: &str) -> Shown {
    printed::start();
    let _ = zedc::run::load(text.as_bytes());
    let said = printed::take()
        .into_iter()
        .filter(|(t, _)| !unsolved(t))
        .map(|(_, text)| text)
        .collect();
    Shown {
        said,
        tops: tops(text),
    }
}

/// The type the checker gives each top-level binding of `text`, and the signature of each of
/// its functions, printed, by name; none when the unit does not reach the checker.
fn tops(text: &str) -> BTreeMap<String, Vec<String>> {
    let Ok((tokens, _)) = zedc::lex::lex_with_docs(text) else {
        return BTreeMap::new();
    };
    let Ok(tree) = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP) else {
        return BTreeMap::new();
    };
    let Ok(stmts) = zedc::ast::unit(text, &tokens, &tree) else {
        return BTreeMap::new();
    };
    let Ok(res) = zedc::resolve::resolve(&stmts) else {
        return BTreeMap::new();
    };
    let info = zedc::check::check(&stmts, &res);
    let mut out: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (name, t) in &info.tops {
        out.entry(name.clone()).or_default().push(t.to_string());
    }
    for (&binder, sig) in &info.sigs {
        let name = &res.binders[binder].name;
        out.entry(name.clone()).or_default().push(sig.to_string());
    }
    for types in out.values_mut() {
        types.sort();
    }
    out
}

/// The comment added: no type depends on it.
const COMMENT: &str = "// a remark that no printed type depends on\n";

/// The bindings added, and the names they bind: a constant and a function whose signature
/// names a type variable, so a variable named from a counter shared across signatures would
/// move the names of every later one. No other type depends on them.
const BINDING: &str = "unrelatedTally = 0;\nunrelatedDouble(positional x) = x + x;\n";
const BOUND: [&str; 2] = ["unrelatedTally", "unrelatedDouble"];

/// `text` with `COMMENT` after its first line that holds code, so every later place moves
/// down a line and, in a unit of one item, into its body.
fn with_comment(text: &str) -> String {
    let mut at = 0;
    for line in text.split_inclusive('\n') {
        at += line.len();
        let code = line.trim();
        if !code.is_empty() && !code.starts_with("//") && !code.starts_with('@') {
            break;
        }
    }
    let mut out = String::with_capacity(text.len() + COMMENT.len());
    out.push_str(&text[..at]);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out.push_str(COMMENT);
    out.push_str(&text[at..]);
    out
}

/// `text` with `BINDING` after its first item, so the items after it come later in the unit.
fn with_binding(text: &str) -> String {
    let at = items(text).cuts[1];
    let mut out = String::with_capacity(text.len() + BINDING.len() + 1);
    out.push_str(&text[..at]);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out.push_str(BINDING);
    out.push_str(&text[at..]);
    out
}

/// `s` with its message types in sorted order: moving items moves the messages, which are
/// printed in order of place, and the types within each message keep their order (order.rs
/// compares the messages themselves).
fn sorted(mut s: Shown) -> Shown {
    s.said.sort();
    s
}

/// Checks each unit whose index is `piece` modulo `PIECES`: alone, then in a batch after the
/// units before it, again, reversed, with a comment and with a binding. Returns how many
/// types were compared.
fn check_piece(piece: usize) -> usize {
    let units = units();
    assert!(units.len() >= 63, "{} units", units.len());
    let mine: Vec<&(String, String)> = units.iter().skip(piece).step_by(PIECES).collect();
    // Alone: each unit on a thread of its own, before anything else is checked there.
    let alone: Vec<Shown> = mine
        .iter()
        .map(|(_, text)| {
            let text = text.clone();
            std::thread::spawn(move || shown(&text)).join().unwrap()
        })
        .collect();
    // What the added bindings print when checked alone.
    let added = shown(BINDING);
    assert_eq!(
        added.tops.get(BOUND[1]).map(Vec::as_slice),
        Some(&["(T) -> T for T in int | f64 | rat".to_string()][..]),
        "{added:?}"
    );
    let mut compared = 0;
    for ((name, text), alone) in mine.into_iter().zip(alone) {
        let batch = shown(text);
        assert_eq!(alone, batch, "{name}: alone, then in a batch");
        assert_eq!(batch, shown(text), "{name}: checked a second time");
        compared += batch.said.len() + batch.tops.len();

        let commented = with_comment(text);
        assert_eq!(
            batch,
            shown(&commented),
            "{name}: with a comment added:\n{commented}"
        );

        let bound = with_binding(text);
        let mut got = shown(&bound);
        // The bindings' own types are printed too when the unit reaches the checker, at their
        // place among the others, as when they are checked alone; every other type is as
        // before.
        if BOUND.iter().any(|b| got.tops.contains_key(*b)) {
            for b in BOUND {
                let own = got.tops.remove(b);
                assert_eq!(own.as_ref(), added.tops.get(b), "{name}: `{b}`:\n{bound}");
            }
            for t in &added.said {
                let at = got.said.iter().position(|s| s == t);
                got.said
                    .remove(at.unwrap_or_else(|| panic!("{name}: `{t}` not printed:\n{bound}")));
            }
        }
        assert_eq!(
            sorted(batch.clone()),
            sorted(got),
            "{name}: with a binding added:\n{bound}"
        );

        let items = items(text);
        let [reversed, _] = items.orders();
        let moved = items.permuted(&reversed).text;
        assert_eq!(
            sorted(batch.clone()),
            sorted(shown(&moved)),
            "{name}: with its items reversed:\n{moved}"
        );
    }
    compared
}

/// The pieces the units are checked in, each a test of its own, so each runs in parallel and
/// within the time of one piece of the suite.
const PIECES: usize = 2;

#[test]
fn printed_types_do_not_move_0() {
    let n = check_piece(0);
    assert!(n > 50, "{n} types compared");
}

#[test]
fn printed_types_do_not_move_1() {
    let n = check_piece(1);
    assert!(n > 50, "{n} types compared");
}

/// Unit `i` of a batch: a generic function, its own constant, and a call whose argument it
/// rejects, so the check prints types both in a signature and in a message.
fn generic_unit(i: usize) -> String {
    format!(
        "scale{i}(positional x) = x + x;\nlimit{i} = {i};\n\
         main(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- String(scale{i}(\"{i}\"));\n}}\n"
    )
}

/// The types printed by a batch of `n` units, each checked after the others, then checked again
/// and with a comment and a binding added, in work linear in the units. The units are built
/// before the timing.
#[test]
fn checking_printed_types_over_a_batch_scales() {
    let first = shown(&generic_unit(3));
    assert_eq!(first.tops["scale3"], ["(T) -> T for T in int | f64 | rat"]);
    assert!(!first.said.is_empty(), "{first:?}");
    let n = 30;
    let batch = |m: usize| -> Vec<String> { (0..m).map(generic_unit).collect() };
    let batches = [batch(n), batch(scaling::FACTOR * n)];
    scaling::check_order("printed types over a batch of n units", n, 1, |m| {
        for text in &batches[usize::from(m != n)] {
            let once = shown(text);
            assert_eq!(once, shown(text));
            assert_eq!(once, shown(&with_comment(text)));
            assert_eq!(once.tops.len() + 2, shown(&with_binding(text)).tops.len());
        }
    });
}

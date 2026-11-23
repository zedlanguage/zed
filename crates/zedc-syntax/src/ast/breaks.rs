//! The placement rule of `break;`, which the parser's grammar does not state.
//!
//! `break;` (DESIGN.md sec:generations, "`break;`") ends the innermost `loop` or `for` whose
//! body holds it directly: in a lambda, in a function or method declared in a loop's body, or
//! with no loop around it, it has no loop to end (row "`break` outside the body of a loop or a
//! `for`").
//!
//! The other placement rule, that a block on a path of an expression statement may export
//! nothing, is `Builder::on_path` in `builder.rs`: `Builder::node` calls it, and a call from
//! `builder.rs` into this file would make the two files import each other (step S.1f).

use super::builder::Builder;
use super::{Error, Note};
use crate::lex::Span;
use zedc_base::rejection::Row;

/// No node: the root has no stop above it.
const NONE: usize = usize::MAX;

impl Builder<'_, '_> {
    /// The nearest node above `n` that decides what a `break;` at `n` ends: a `Loop` or a `For`
    /// whose body holds `n`, or a `Lambda`, `Function` or `Method` that holds it. `None` when
    /// there is none up to the root.
    // Complexity tradeoff: the naive test climbs from each `break;` to the root, O(depth) per
    // `break;` and O(n · depth) for a tree of n nodes; listing the stop of every node in one
    // walk from the root, on the first `break;`, costs O(n) once and O(1) per `break;` after.
    fn stop_of(&self, n: usize) -> Option<usize> {
        let tree = self.tree;
        let stops = self.stops.get_or_init(|| {
            let mut stops = vec![NONE; tree.nodes.len()];
            let mut stack = vec![tree.root];
            while let Some(k) = stack.pop() {
                let kids = &tree.nodes[k].kids;
                for (i, &c) in kids.iter().enumerate() {
                    // The body of a `loop` or a `for` is its last child; a `for`'s source and
                    // guard are not in its body.
                    stops[c] = match tree.name(k) {
                        "Loop" | "For" if i + 1 == kids.len() => k,
                        "Lambda" | "Function" | "Method" => k,
                        _ => stops[k],
                    };
                }
                stack.extend(kids);
            }
            stops
        });
        stops.get(n).copied().filter(|&s| s != NONE)
    }

    /// The error for the `break;` of node `d` when no `loop` or `for` body holds it directly.
    /// In a string hole, whose tree holds only the hole, a `break;` with no lambda or function
    /// around it within the hole is accepted: whether a loop's body holds the string is not
    /// known here. No program holding one runs, though, so accepting it here decides no
    /// verdict. Name resolution refuses every `break;` it walks until layer L6 (`zedc-resolve`
    /// `Resolver::stmt`, `StmtKind::Break`, "a `break`"), and its walk of an expression enters
    /// a string's holes (`ExprKind::Str`) and every block in them; and where a walk passes a
    /// part by (a `loop`, which it refuses whole, or the section of a fold `><`), the checker
    /// and elaboration give a `break;` no meaning (`StmtKind::Break` is `unreachable!` in
    /// `zedc-check` `check/walk.rs` and `zedc-elab` `elab/walk.rs`), so the compiler stops
    /// rather than run the program. Tested by
    /// `l06_01_parser::later::a_break_in_a_string_hole_is_refused_by_name_resolution`.
    pub(super) fn break_placed(&self, d: usize) -> Result<(), Error> {
        let stop = self.stop_of(d);
        match stop.map(|s| self.tree.name(s)) {
            Some("Loop" | "For") => Ok(()),
            None if self.tree.name(self.tree.root) != "Unit" => Ok(()),
            _ => Err(self.break_outside(d, stop)),
        }
    }

    /// The error for the generation push `x' <- value` of target node `t` when no `loop` and
    /// no method holds it (DESIGN.md sec:ports, "What a push may name"; row "Generation push
    /// outside a loop"). A lambda or a `for` in a loop's body runs as part of the loop's step,
    /// so a push in one is a push of the loop (sec:generations), and a method writes its
    /// receiver's next value through primed fields; those stay for name resolution. In a string
    /// hole, whose tree holds only the hole, the push is accepted here, as `break;` is.
    // Complexity tradeoff: climbing from each push to the root costs O(depth) per push, O(n ·
    // depth) in all; one walk from the root on the first generation push marks every node a
    // `loop` or method holds, O(n) once and O(1) per push after.
    pub(super) fn generation_push_placed(
        &self,
        t: usize,
        x: &str,
        value: &str,
    ) -> Result<(), Error> {
        let tree = self.tree;
        if tree.name(tree.root) != "Unit" {
            return Ok(());
        }
        let held = self.in_loops.get_or_init(|| {
            let mut held = vec![false; tree.nodes.len()];
            let mut stack = vec![tree.root];
            while let Some(k) = stack.pop() {
                let inside = held[k] || matches!(tree.name(k), "Loop" | "Method");
                for &c in &tree.nodes[k].kids {
                    held[c] = inside;
                }
                stack.extend(&tree.nodes[k].kids);
            }
            held
        });
        if held[t] {
            return Ok(());
        }
        let span = self.span(t);
        Err(Error {
            row: Some(Row::GenerationPushOutsideLoop),
            menu: String::new(),
            span,
            message: format!(
                "Invalid push to `{x}'` outside a loop: only the body of a `loop`, or of a method \
                 for a field of its receiver, writes a next generation."
            ),
            notes: vec![Note {
                span,
                text: format!("repair: `{x} = {value};`").into(),
            }],
        })
    }

    /// The name a lambda of node `l` is bound to, `f` in `f = x -> …;`, if it is the whole
    /// value of a binding of one name.
    fn lambda_name(&self, l: usize) -> Option<&str> {
        let e = self.parent(l)?;
        let b = self.parent(e)?;
        let target = match (self.tree.name(b), self.kids(b)) {
            ("PlainBinding", &[t, v]) if v == e => t,
            ("TypedBinding", &[t, _, v]) if v == e => t,
            _ => return None,
        };
        Some(self.word(self.tree.nodes[target].start)).filter(|&w| w != "_")
    }

    fn break_outside(&self, d: usize, stop: Option<usize>) -> Error {
        let span = self.span(d);
        let tree = self.tree;
        // The loop around the lambda or function, the first `loop` or `for` body up the stops.
        let mut around = stop;
        while let Some(k) = around.filter(|&k| !matches!(tree.name(k), "Loop" | "For")) {
            around = self.stop_of(k);
        }
        let short = |s: Span| {
            let text = &self.text[s.start..s.end];
            match text.lines().next() {
                Some(first) if first.len() < text.len() => format!("{} …", first.trim_end()),
                _ => text.to_string(),
            }
        };
        let mut notes = Vec::new();
        let (what, call) = match stop.map(|s| (s, tree.name(s))) {
            Some((s, "Lambda")) => match self.lambda_name(s) {
                Some(f) => (format!("the lambda `{f}`"), format!("{f}(…)")),
                None => ("a lambda".to_string(), "f(…)".to_string()),
            },
            Some((s, "Function")) => {
                let f = self.word(tree.nodes[self.kids(s)[0]].start);
                (format!("the function `{f}`"), format!("{f}(…)"))
            }
            Some((s, _)) => {
                let k = self.kids(s);
                let r = self.word(tree.nodes[k[0]].start);
                let m = self.word(tree.nodes[k[1]].start);
                (format!("the method `{r}.{m}`"), format!("x.{m}(…)"))
            }
            None => (String::new(), String::new()),
        };
        if let Some(s) = stop {
            let text = match around {
                Some(_) => {
                    format!("{what}, declared in the loop's body; its body is not the loop's")
                }
                None => format!("{what}, with no `loop` or `for` around the `break;` inside it"),
            };
            notes.push(Note {
                span: self.span(s),
                text: format!("`{}` is {text}", short(self.span(s))).into(),
            });
        }
        let headline = match (stop, around) {
            (Some(_), Some(l)) => {
                notes.push(Note {
                    span: self.span(l),
                    text: format!(
                        "the loop around {what}, which a `break;` ends only from the loop's own body"
                    ).into(),
                });
                notes.push(Note {
                    span,
                    text: format!(
                        "repair: return a result that the loop's body tests, as `done = {call}; \
                         if done {{ break; }};`"
                    )
                    .into(),
                });
                notes.push(Note {
                    span,
                    text: format!("repair: move the `break;` out of {what}, into the loop's body")
                        .into(),
                });
                format!(
                    "Invalid use of `break;` in {what}: it ends only a loop whose own body holds it."
                )
            }
            (Some(_), None) => {
                notes.push(Note {
                    span,
                    text: format!("repair: `return e;`, which ends {what} with the value `e`")
                        .into(),
                });
                format!(
                    "Invalid use of `break;` outside a loop: {what} has no `loop` or `for` around it."
                )
            }
            (None, _) => {
                notes.push(Note {
                    span,
                    text:
                        "repair: delete the `break;`, or move it into the body of a `loop` or `for`"
                            .into(),
                });
                "Invalid use of `break;` outside a loop: it ends only a `loop` or `for` whose body holds it."
                    .to_string()
            }
        };
        Error {
            row: Some(Row::BreakOutsideLoop),
            menu: String::new(),
            span,
            message: headline,
            notes,
        }
    }
}

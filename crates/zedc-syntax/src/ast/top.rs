//! A statement at a unit's top level (DESIGN.md sec:units, "A unit's top level holds
//! declarations only"; sec:diagnostics, row "Statement at a unit's top level"; plan row
//! TOP-statements-reject). The grammar's `Unit = Item*` lets `Decl` hold eight kinds of
//! statement, a push, `emit`, `while`, `until`, `break`, `return`, an `if` statement and an
//! expression statement, and the grammar stays so: the builder names the statement and moves it
//! into `main` in its repair, where a parse error could only say which token it stopped at.

use super::builder::Builder;
use super::{Error, Note};
use crate::lex::Span;
use zedc_base::rejection::Row;

/// The grammar's rules for the eight kinds of statement `Decl` takes (syntax.peg): each is the
/// node an `Item` holds, since every alternative of `Decl` is written `~Rule`.
const STATEMENTS: [&str; 10] = [
    "WholePush",
    "KeyedPush",
    "AckPush",
    "Emit",
    "While",
    "Until",
    "Break",
    "Return",
    "IfStmt",
    "ExprStmt",
];

impl Builder<'_, '_> {
    /// The error for item `k` of the unit's top level when it holds a statement, through any
    /// `local` and annotations, else `None`; `main` keeps [`Builder::top_main`] once found.
    // Complexity tradeoff: O(size of the statement's text), to quote it, and the walk of the
    // top level for `main` once per unit, O(items), kept in `main` rather than walked again
    // per statement, which would cost O(items × statements).
    pub(super) fn top_statement(
        &self,
        k: usize,
        main: &mut Option<(String, String)>,
    ) -> Option<Error> {
        let mut d = self.kids(k)[0];
        loop {
            match self.tree.name(d) {
                "Local" => d = self.kids(d)[0],
                "Annotated" => d = *self.kids(d).last().expect("Annotated ends in a Decl"),
                _ => break,
            }
        }
        let rule = self.tree.name(d);
        if !STATEMENTS.contains(&rule) {
            return None;
        }
        let span = self.span(d);
        let stmt = &self.text[span.start..span.end];
        // A statement on more than one line, or holding a backtick, is not quoted: the excerpt
        // under the headline shows it, as for a syntax error (`Error::of_parse`).
        let quotable = !stmt.contains(['\n', '`']);
        let (header, param) = main.get_or_insert_with(|| self.top_main());
        let moved = format!("{header} {{ {stmt} }}");
        let message = match quotable {
            true => format!(
                "Statement at the top level of the unit: `{stmt}`. Move it into the body of \
                 `main`, as in `{moved}`."
            ),
            false => {
                "Statement at the top level of the unit. Move it into the body of `main`.".into()
            }
        };
        let note = |text: String| Note { span, text };
        let mut notes = vec![note(
            "a unit's top level holds declarations, which take any order and run in no frame; \
             a statement has an order and runs in a frame, so it stands in a body"
                .into(),
        )];
        if let Some(t) = self
            .kids(d)
            .iter()
            .find(|&&t| self.tree.name(t) == "PushTarget")
        {
            let s = self.span(*t);
            let port = &self.text[s.start..s.end];
            notes.push(note(match port.strip_prefix(&format!("{param}.")) {
                Some(_) => format!(
                    "`{port}` is a field of `{param}`, the parameter of `main`, and is a port \
                     only in `main`'s body"
                ),
                None => format!(
                    "`{port}` is no port here: a program's ports are the fields of `{param}`, \
                     the parameter of `main`, as `{param}.stdout`"
                ),
            }));
        }
        if quotable {
            notes.push(note(format!("repair: `{moved}`")));
        }
        if rule == "ExprStmt" {
            let e = self.span(self.kids(d)[0]);
            let value = &self.text[e.start..e.end];
            if quotable {
                notes.push(note(format!(
                    "repair: `value = {value};`, to keep the value"
                )));
            }
            notes.push(note(
                "repair: delete the statement; nothing reads its value".into(),
            ));
        }
        Some(Error {
            row: Some(Row::TopLevelStatement),
            menu: String::new(),
            span,
            message,
            notes,
        })
    }

    /// The header of the unit's `main` as written, `main(m: MainArgs)` where it has none, and
    /// the name of its parameter, `m` where it has none written.
    fn top_main(&self) -> (String, String) {
        let found = self.kids(self.tree.root).iter().find_map(|&k| {
            let d = self.kids(k)[0];
            let d = match self.tree.name(d) {
                "Annotated" => *self.kids(d).last()?,
                _ => d,
            };
            let node = &self.tree.nodes[d];
            (self.tree.name(d) == "Function" && self.word(node.start) == "main")
                .then(|| self.mains.at(self.span(d).end - 1))
                .flatten()
        });
        match found {
            Some(b) => {
                let Span { start, end } = b.header;
                let param = b.param.clone().unwrap_or_else(|| "m".into());
                (self.text[start..end].to_string(), param)
            }
            None => ("main(m: MainArgs)".into(), "m".into()),
        }
    }
}

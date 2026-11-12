//! The message for a boundary clause written in a test case, as `test { 1 with x = 0 -> 1 }`
//! (item FIX-testcase-with-value). A test case is `Expr12 '->' Expr12` (DESIGN.md
//! sec:grammar), and inside an expression `with` begins only a facet `with f(…)` or an update
//! `with { … }`, so a test case takes no boundary clause: the parse stops in its first item,
//! and the clause is refused whole, at its `with`.

use zedc_base::rejection::Row;

use super::clause::{Clause, Toks, depth, reaches};
use super::engine::{Node, Parser};
use super::grammar::Kind;
use crate::lex::Span;

/// What starts an item of a `with` clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ItemHead {
    /// `x =`, with neither `initial` nor an index.
    Bare,
    /// `initial x =`.
    Initial,
    /// `x[k] =`, one or more indices.
    Indexed,
}

/// The kind of item that starts at token `i` of `toks`, and the token its value starts at:
/// `initial x =`, `x[k]… =` or `x =`. The scan over the brackets of an index stops at the end
/// of the tokens.
fn item_head(toks: &[(Kind, &str)], i: usize) -> Option<(ItemHead, usize)> {
    let at = |k: usize| toks.get(k).copied().unwrap_or((Kind::End, ""));
    // `initial` is a reserved word, a keyword token.
    if at(i).1 == "initial" {
        return (at(i + 1).0 == Kind::Ident && at(i + 2).1 == "=")
            .then_some((ItemHead::Initial, i + 3));
    }
    if at(i).0 != Kind::Ident {
        return None;
    }
    match at(i + 1).1 {
        "=" => Some((ItemHead::Bare, i + 2)),
        "[" => {
            let mut k = i + 1;
            while at(k).1 == "[" {
                let mut d = 0;
                loop {
                    let t = at(k);
                    if t.0 == Kind::End {
                        return None;
                    }
                    d += depth(t.1);
                    k += 1;
                    if d == 0 {
                        break;
                    }
                }
            }
            (at(k).1 == "=").then_some((ItemHead::Indexed, k + 1))
        }
        _ => None,
    }
}

/// The [`Clause`] for a `with` clause in a test case at whose first item a parse failed (token
/// `far`): `with` before the item, and the `{` of `test {` as the bracket around it. No rule
/// reads an item of a `with` clause after an expression, so `with x =` and `with x[k] =` each
/// fail one token after the item's first word, where a facet `with f(…)` wants its `(`, and
/// `with initial x =` fails at the reserved word `initial`. Each item's value is matched as an
/// `Expr12`, the rule of a side of a test case (`TestCase = Expr12 '->' Expr12`), so the case's
/// `->` ends it as it ends the left side.
///
/// Cost, on the error path only: a scan back to the table's `{` and forward to the case's end;
/// one packrat parser for the values and the case's left side, linear in what it reads; at
/// most two parses of the unit with the clause rewritten; and one walk down the tree from the
/// root to the case. Linear in the unit.
pub(super) fn case_item(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    // Complexity tradeoff: the naive way reparses each case of the table on its own as a
    // `TestCase` to find the one that fails, O(cases × unit); here the case is cut out by one
    // scan back from `with` and one forward at bracket depth 0, O(unit), and only its values and
    // left side are parsed.
    let toks = t.toks;
    let w = if t.t(far) == "initial" {
        far.checked_sub(1)?
    } else {
        far.checked_sub(2)?
    };
    if toks[w] != (Kind::Keyword, "with") {
        return None;
    }
    item_head(toks, w + 1)?;
    // Back to the bracket around the case; the case starts after the nearest `,` at its depth.
    let mut open = w;
    let mut first = None;
    let mut d = 0;
    while open > 0 {
        let s = toks[open - 1].1;
        if d - depth(s) < 0 {
            break;
        }
        if d == 0 && s == "," && first.is_none() {
            first = Some(open);
        }
        d -= depth(s);
        open -= 1;
    }
    if open < 2 || toks[open - 1].1 != "{" || toks[open - 2] != (Kind::Keyword, "test") {
        return None;
    }
    let open = open - 1;
    let first = first.unwrap_or(open + 1);
    let e12 = t.g.rule("Expr12")?;
    let mut p = Parser::new(t.g, t.ring, toks);
    // Each item: its first token, what starts it, the token its value starts at, and the token
    // after its value.
    let mut items: Vec<(usize, ItemHead, usize, usize)> = Vec::new();
    let mut i = w + 1;
    while let Some((h, v)) = item_head(toks, i) {
        let (e, _) = p.rule_node(e12, v, false)?;
        items.push((i, h, v, e));
        if toks[e].1 != "," {
            break;
        }
        i = e + 1;
    }
    let cut = items.last()?.3;
    // Forward to the `,` or `}` that ends the case.
    let mut stop = cut;
    let mut d = 0;
    while toks[stop].0 != Kind::End
        && !(d == 0 && toks[stop].1 == ",")
        && d + depth(toks[stop].1) >= 0
    {
        d += depth(toks[stop].1);
        stop += 1;
    }
    let (l, _) = p.rule_node(e12, first, false)?;
    let arrow = if l == w {
        (toks[cut].1 == "->").then_some(cut)
    } else {
        (l < w && toks[l].1 == "->").then_some(l)
    };
    let before = arrow.filter(|&a| a < w).map_or(first, |a| a + 1);
    // The clause deleted: the menu's first repair, and the tree the function's name is read
    // from.
    let mut fixed = toks[..w].to_vec();
    fixed.extend_from_slice(&toks[cut..]);
    let mut q = Parser::new(t.g, t.ring, fixed.as_slice());
    let (deleted, function) = match q.rule_node(t.start, 0, false) {
        Some((e, root)) if e + 1 >= fixed.len() => (true, enclosing(t, &q.nodes, root, w)),
        Some((e, _)) => (e.max(q.far) > w, None),
        None => (q.far > w, None),
    };
    // The clause as an update of fields: only items `x = e`, after code that can be a struct.
    let literal = matches!(
        &toks[before..w],
        [(
            Kind::Int | Kind::Float | Kind::Rat | Kind::Str | Kind::Atom,
            _
        )] | [(_, "-"), (Kind::Int | Kind::Float | Kind::Rat, _)]
            | [(Kind::Keyword, "true" | "false")]
    );
    let update = !literal && items.iter().all(|it| it.1 == ItemHead::Bare) && {
        let mut fixed = toks[..=w].to_vec();
        fixed.push((toks[open].0, "{"));
        fixed.extend_from_slice(&toks[w + 1..cut]);
        fixed.push((toks[open].0, "}"));
        fixed.extend_from_slice(&toks[cut..]);
        reaches(t.g, t.ring, t.start, &fixed, cut + 1)
    };

    // The text of tokens `a` to `b`, `b` not included; empty when there are none.
    let sl = |a: usize, b: usize| if b > a { t.between(a, b - 1) } else { "" };
    let glue = |a: &str, b: &str| match (a.is_empty(), b.is_empty()) {
        (_, true) => a.to_string(),
        (true, _) => b.to_string(),
        _ => format!("{a} {b}"),
    };
    let (i0, h0, v0, e0) = items[0];
    let rest = sl(cut, stop);
    let sides = arrow.and_then(|a| {
        let sides = if a == cut {
            (sl(first, w).to_string(), sl(a + 1, stop).to_string())
        } else {
            (sl(first, a).to_string(), glue(sl(a + 1, w), rest))
        };
        (!sides.0.is_empty() && !sides.1.is_empty()).then_some(sides)
    });
    let function = function.map(|(f, method)| match method {
        true => format!("{}.{}", toks[f].1, toks[f + 2].1),
        false => toks[f].1.to_string(),
    });
    let case = sl(first, stop);
    let case_span = Span {
        start: t.span(first).start,
        end: t.span(stop - 1).end,
    };
    let clause = sl(w, cut);
    let clause_span = Span {
        start: t.span(w).start,
        end: t.span(cut - 1).end,
    };
    let before_text = sl(before, w);
    let head = sl(i0, v0);
    let name = toks[i0 + usize::from(h0 == ItemHead::Initial)].1;
    let value = sl(v0, e0);
    let of_kind = |k: ItemHead| {
        items
            .iter()
            .find(|it| it.1 == k)
            .map(|&(i, _, v, e)| (toks[i + usize::from(k == ItemHead::Initial)].1, sl(v, e)))
    };
    let bare = of_kind(ItemHead::Bare);
    let initial = of_kind(ItemHead::Initial);

    let of = function
        .as_ref()
        .map(|f| format!(" of `{f}`"))
        .unwrap_or_default();
    let mut message = format!(
        "The test case `{case}`{of} holds the boundary clause `{clause}`, and a test case takes no \
         boundary clause."
    );
    if let Some((a, b)) = &sides {
        message.push_str(&match function.as_deref() {
            Some("main") => format!(
                " It states that a wave of `main` reading the ports `{a}` writes the bytes `{b}`."
            ),
            Some(f) => format!(" It states that `{f}` applied to `{a}` gives `{b}`."),
            None => format!(
                " It states that the function the table follows, applied to `{a}`, gives `{b}`."
            ),
        });
    }
    message.push_str(&format!(
        " Each side of a test case is an expression, and in an expression `with` is followed only \
         by a facet, as `{before_text} with f(…)`, or by an update of fields, as `{before_text} \
         with {{ {name} = … }}`; here `with` is followed by `{head}`, which begins a boundary \
         item. A boundary clause follows only the value of an indexed definition, each item \
         with its key, as `{name}[i in 0..<n] = … with {name}[-1] = {value};`, and a variable \
         a loop updates \
         takes its sentinel value, its value before step 0, from a statement of the loop's body, \
         `initial {name} = {value};`."
    ));
    if arrow == Some(cut) {
        message.push_str(&format!(
            " The item is read as `{}`: its value ends before `->`, the arrow of the test case.",
            sl(i0, e0)
        ));
    }
    if let Some((n, v)) = bare {
        message.push_str(&format!(
            " Written with neither `initial` nor a key, `with {n} = {v}` would be refused on a \
             statement of a loop too: it reads as though `{n}` took the value `{v}` anew on every \
             step."
        ));
    }
    if let Some((n, v)) = initial {
        message.push_str(&format!(
            " `with initial {n} = {v}` would be refused on a statement of a loop too: `with \
             initial` is no longer how a sentinel value is given, and the statement `initial {n} \
             = {v};` gives it."
        ));
    }

    let mut notes = vec![
        (
            Span {
                start: t.span(open - 1).start,
                end: t.span(open).end,
            },
            "the test table that holds the case".to_string(),
        ),
        (
            case_span,
            "the test case, which takes no boundary clause".to_string(),
        ),
    ];
    if deleted {
        notes.push((
            case_span,
            format!(
                "repair: `{}`, the case with the `with` clause deleted",
                glue(sl(first, w), rest)
            ),
        ));
    }
    if update {
        let u = glue(
            &format!("{} {{ {} }}", sl(first, w + 1), sl(w + 1, cut)),
            rest,
        );
        notes.push((
            case_span,
            format!("repair: `{u}`, the case with `{before_text}` updated in its fields"),
        ));
    }
    let row = if bare.is_some() {
        Some(Row::BareBoundary)
    } else if initial.is_some() {
        Some(Row::WithInitialItem)
    } else {
        None
    };
    Some(Clause {
        row,
        message,
        span: clause_span,
        notes,
    })
}

/// The first token of the innermost `Function` or `Method` node of the tree under `root` whose
/// span holds token `at`, and whether it is a method. One walk from the root down the nodes
/// that hold `at`, each step a scan of one node's kids: linear in the tree.
fn enclosing(t: &Toks<'_, '_>, nodes: &[Node], root: usize, at: usize) -> Option<(usize, bool)> {
    let mut n = root;
    let mut found = None;
    loop {
        let node = &nodes[n];
        match t.g.rules[node.rule].name.as_str() {
            "Function" => found = Some((node.start, false)),
            "Method" => found = Some((node.start, true)),
            _ => {}
        }
        let holds = |&&k: &&usize| nodes[k].start <= at && at < nodes[k].end;
        match node.kids.iter().find(holds) {
            Some(&k) => n = k,
            None => return found,
        }
    }
}

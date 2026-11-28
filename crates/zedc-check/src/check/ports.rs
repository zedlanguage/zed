//! Output ports passed to functions (DESIGN.md L1.19): "a function other than `main` takes a
//! port as an argument, `say(positional s, out: Lines) { out <- s; }` called as
//! `say("hi", out: m.stdout)`, and the port's direction is the field's". A parameter declared
//! `Lines` is an output port of its function when the body pushes to it, or passes it whole to
//! a parameter that is an output port; any other `Lines` parameter is an input, a value read.
//! Passing an output port whole to an output port parameter is not a read. Every other use of
//! an output port, `main`'s (`m.stdout`, `m.stderr`) or a parameter's, reads it and is
//! rejected, as is a push to a name that is no output port, an argument for an output port
//! parameter that is no output port, and a function with output port parameters named other
//! than as the callee of a call, which could reach its parameters with other values.
//!
//! The elaborator then needs no copy of a function per port it is passed: the argument is the
//! port's name, and a push to the parameter pushes to whichever of `main`'s output ports the
//! name is (`zedc_elab`, `Frame::Push`).

use std::collections::{HashMap, HashSet};

use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Kind, Ref, Resolution};
use zedc_syntax::ast::{Expr, ExprKind, Note, StmtKind, TypeKind};
use zedc_syntax::lex::Span;

/// The output port parameters of a unit and the errors of its uses of output ports.
pub struct Ports {
    /// The binder of each parameter that is an output port.
    pub params: HashSet<usize>,
    /// The binder of each declared function with an output port parameter: a call of one
    /// pushes to the port it is given, and so is a statement ([`silent_tail`]).
    pub writers: HashSet<usize>,
    /// Each error: its place, its headline and its notes.
    pub errors: Vec<(Span, String, Vec<Note>)>,
    /// Each push to a name that is not a port, as `errors` (row "Push to a name that is not a
    /// port", DESIGN.md sec:ports, "What a push may name").
    pub not_ports: Vec<(Span, String, Vec<Note>)>,
    /// The text of the argument of each call of a declared function that fills a parameter,
    /// by the text of the call and the parameter's binder (read by the module `twice`).
    pub args: HashMap<(Span, usize), Span>,
}

/// What an argument of a call of a declared function fills.
struct Arg {
    /// The argument's text.
    span: Span,
    /// The text of the whole call.
    call: Span,
    /// The function called.
    callee: usize,
    /// The parameter it fills, by its binder.
    param: usize,
}

/// The output port parameters of the unit whose tables are `t`, and the errors of its uses
/// of output ports.
// Complexity tradeoff: the naive method decides each `Lines` parameter on its own, following
// the parameters it is passed to until it meets a push, O(P·(P+A)) for P parameters and A
// arguments (a chain of n helpers each passing its port to the next is O(n²)). Used: the
// pushes mark their parameters, and one search backward over the edges "argument parameter →
// parameter it fills" marks the rest, each parameter once (the set of marked parameters is the
// visited set): O(P + A + U) with the checks over the U uses of names, the work of reading the
// resolution once. Test:
// `l01_19_whole_file_ports::ports::a_chain_of_helpers_passing_a_port_scales`.
pub fn ports(t: &Tables<'_>) -> Ports {
    let res = t.res;
    let bound = |span: &Span| match res.uses.get(span) {
        Some(Ref::Bound(ids)) => Some(ids),
        _ => None,
    };
    let mut errors = Vec::new();
    // Each parameter of a declared function other than `main`: its function and its place.
    let mut of: HashMap<usize, (usize, usize)> = HashMap::new();
    for (&f, decl) in &t.funcs {
        if decl.main.is_some() {
            continue;
        }
        for (i, p) in decl.params.iter().enumerate() {
            if let Some(&b) = t.ids.get(&(p.span, p.name.as_str())) {
                of.insert(b, (f, i));
            }
        }
    }
    let param = |b: usize| of.get(&b).map(|&(f, i)| (f, &t.funcs[&f].params[i]));
    let lines = |b: usize| param(b).is_some_and(|(_, p)| is_lines(p.ty.as_ref().map(|t| &t.kind)));
    let main_port = |b: usize| res.binders[b].kind == Kind::Port;

    // The pushes: each to a port of `main`, or a parameter declared `Lines`, which is then an
    // output port.
    let mut params: HashSet<usize> = HashSet::new();
    let mut todo: Vec<usize> = Vec::new();
    let mut first_push: HashMap<usize, Span> = HashMap::new();
    let mut not_ports = Vec::new();
    for &s in &res.pushes {
        let ids = match res.uses.get(&s) {
            Some(Ref::Bound(ids)) => ids,
            Some(Ref::Prelude(n)) => {
                not_ports.push((
                    s,
                    format!(
                        "Invalid push to `{n}`, a prelude word: a push goes to a port or a \
                         declared accumulator."
                    ),
                    vec![Note {
                        span: s,
                        text: "repair: `m.stdout <- …;` in `main`".into(),
                    }],
                ));
                continue;
            }
            _ => continue,
        };
        let b = ids[0];
        let name = &res.binders[b].name;
        match param(b) {
            _ if main_port(b) => {}
            Some(_) if lines(b) => {
                first_push.entry(b).or_insert(s);
                if params.insert(b) {
                    todo.push(b);
                }
            }
            Some((f, p)) => {
                // Taken for an output port all the same, so that its calls are checked as
                // the calls of one, and the one error is this.
                first_push.entry(b).or_insert(s);
                if params.insert(b) {
                    todo.push(b);
                }
                not_ports.push((
                    s,
                    format!(
                        "Invalid push to `{name}`, a parameter of `{}` not declared `Lines`. Try \
                         `{name}: Lines` instead.",
                        res.binders[f].name
                    ),
                    vec![
                        Note {
                            span: p.span,
                            text: format!("the parameter `{name}`").into(),
                        },
                        Note {
                            span: p.span,
                            text: format!("repair: `{name}: Lines`").into(),
                        },
                    ],
                ))
            }
            None => not_ports.push((
                s,
                format!(
                    "Invalid push to `{name}`, {}: a push goes to a port or a declared \
                     accumulator.",
                    what(res.binders[b].kind)
                ),
                vec![Note {
                    span: s,
                    text: "repair: `m.stdout <- …;` in `main`, or a parameter declared `Lines` \
                           that `main` passes `m.stdout` to"
                        .into(),
                }],
            )),
        }
    }

    // The arguments of calls of declared functions, and the edges from a `Lines` parameter
    // passed whole to the parameter it fills.
    let mut args: Vec<Arg> = Vec::new();
    let mut callees: HashSet<Span> = HashSet::new();
    let mut fed: HashMap<usize, Vec<usize>> = HashMap::new();
    // Each called function's named parameters, by name: the first of each name, as a search
    // of its parameters in order finds it. Complexity tradeoff: built once per function
    // called, O(P) for its P parameters, then O(1) expected per named argument. The naive
    // way, a search of the parameters for each named argument, is O(P) an argument, O(n²)
    // for a call naming its n parameters: the whole check of l01_16's `named(n)` took 8.5 s
    // at n = 64000 against 0.32 s at 8000, 26.9 times for 8 times n (b28 job j10), three
    // quarters of it in that search (perf at 64000, job j11). Test:
    // `l01_16_elaboration::bench::a_call_naming_many_arguments_is_checked_in_linear_time`.
    let mut by_name: HashMap<usize, HashMap<&str, usize>> = HashMap::new();
    for c in &res.calls {
        callees.insert(c.callee);
        let Some(ids) = bound(&c.callee) else {
            continue;
        };
        for &f in ids.iter() {
            let Some(decl) = t.funcs.get(&f) else {
                continue;
            };
            let names = by_name.entry(f).or_insert_with(|| {
                let mut names = HashMap::new();
                for (i, p) in decl.params.iter().enumerate() {
                    if !p.positional {
                        names.entry(p.name.as_str()).or_insert(i);
                    }
                }
                names
            });
            let slots = (c.positional.iter().enumerate())
                .filter_map(|(i, &a)| decl.params.get(i).filter(|p| p.positional).map(|p| (a, p)))
                .chain(
                    c.named
                        .iter()
                        .filter_map(|(n, a)| names.get(n.as_str()).map(|&i| (*a, &decl.params[i]))),
                );
            for (span, p) in slots {
                let Some(&q) = t.ids.get(&(p.span, p.name.as_str())) else {
                    continue;
                };
                if let Some(a) = bound(&span).map(|ids| ids[0]).filter(|&a| lines(a)) {
                    fed.entry(q).or_default().push(a);
                }
                args.push(Arg {
                    span,
                    call: c.span,
                    callee: f,
                    param: q,
                });
            }
        }
    }
    // A parameter passed whole to an output port parameter is one.
    while let Some(q) = todo.pop() {
        for &a in fed.get(&q).into_iter().flatten() {
            if params.insert(a) {
                todo.push(a);
            }
        }
    }
    let port = |b: usize| main_port(b) || params.contains(&b);
    let code = |span: Span| {
        (t.text)
            .and_then(|s| s.get(span.start..span.end))
            .and_then(zed_kernel::text::prose::one_line_only)
    };
    let main = t.funcs.values().find(|f| f.main.is_some());
    let m = main.and_then(|f| f.main.as_ref()?.param.as_ref().map(|(m, ..)| m.as_str()));

    // Each argument for an output port parameter is an output port; each output port passed
    // as an argument fills one.
    let mut passed: HashSet<Span> = HashSet::new();
    for a in &args {
        let to_port = params.contains(&a.param);
        let from_port = bound(&a.span).map(|ids| ids[0]).filter(|&b| port(b));
        passed.insert(a.span);
        let (callee, p) = (&res.binders[a.callee].name, &res.binders[a.param].name);
        match (to_port, from_port) {
            (true, None) => {
                let call = code(a.call);
                let inside_main = main.is_some_and(|f| within(a.span, f.body.span));
                let fix = match (call, m) {
                    (Some(c), Some(m)) if inside_main => {
                        let at = a.span.start - a.call.start..a.span.end - a.call.start;
                        let mut fixed = c.to_string();
                        fixed.replace_range(at, &format!("{m}.stdout"));
                        Some(fixed)
                    }
                    _ => None,
                };
                let shown = call.map_or(String::new(), |c| format!(": `{c}`"));
                let try_ = fix.map_or(String::new(), |f| format!(" Try `{f}` instead."));
                errors.push((
                    a.span,
                    format!(
                        "`{callee}` pushes to `{p}`, so `{p}` takes an output port{shown}.{try_}"
                    ),
                    vec![
                        Note {
                            span: first_push.get(&a.param).copied().unwrap_or(a.span),
                            text: format!(
                                "`{p}` is an output port of `{callee}`, pushed to and never read"
                            )
                            .into(),
                        },
                        Note {
                            span: a.span,
                            text: "repair: pass `m.stdout` or `m.stderr` from `main`, or an \
                                   output port parameter of the caller"
                                .into(),
                        },
                    ],
                ));
            }
            (false, Some(b)) => {
                let name = &res.binders[b].name;
                let shown = code(a.call).map_or(String::new(), |c| format!(": `{c}`"));
                errors.push((
                    a.span,
                    format!(
                        "`{name}` is an output port, pushed to and never read, and `{callee}` \
                         reads `{p}`{shown}."
                    ),
                    vec![
                        Note {
                            span: res.binders[a.param].span,
                            text: format!(
                                "`{callee}` never pushes to `{p}`, as `{p} <- lines;`, so `{p}` \
                                 is a value it reads"
                            )
                            .into(),
                        },
                        Note {
                            span: a.span,
                            text: format!(
                                "repair: push to `{p}` in `{callee}`, as `{p} <- lines;`, or \
                                 pass `{callee}` the lines to write and push them to `{name}` \
                                 here"
                            )
                            .into(),
                        },
                    ],
                ));
            }
            _ => {}
        }
    }

    // The first output port parameter of each function that has one.
    let mut outs: HashMap<usize, (usize, &str)> = HashMap::new();
    for &b in &params {
        let (f, i) = of[&b];
        let e = outs.entry(f).or_insert((i, &res.binders[b].name));
        if i < e.0 {
            *e = (i, &res.binders[b].name);
        }
    }

    // Every other use of an output port reads it; a function with output port parameters is
    // named only as a callee.
    let pushes: HashSet<Span> = res.pushes.iter().copied().collect();
    for (&span, r) in &res.uses {
        let Ref::Bound(ids) = r else { continue };
        let b = ids[0];
        if port(b) {
            if pushes.contains(&span) || passed.contains(&span) {
                continue;
            }
            let name = &res.binders[b].name;
            let notes = match first_push.get(&b) {
                Some(&at) => vec![Note {
                    span: at,
                    text: format!("`{name}` is pushed to here").into(),
                }],
                None => Vec::new(),
            };
            let mut notes = notes;
            notes.push(Note {
                span,
                text: format!(
                    "repair: push to `{name}`, as `{name} <- lines;`, or pass it whole to a \
                     parameter that is pushed to"
                )
                .into(),
            });
            // The builder's guidance for a read of an output of `main`, which it rejects
            // wherever the read is not a whole argument.
            if let (true, Some(m)) = (main_port(b), m) {
                notes.push(Note {
                    span,
                    text: format!(
                        "repair: to read the program's input, read `{m}.stdin`, `{m}.args` or \
                         `{m}.env`; to use lines this program computes, read them from the \
                         binding that holds them before it pushes them"
                    )
                    .into(),
                });
            }
            errors.push((
                span,
                format!(
                    "`{name}` is an output port, pushed to and never read, and it is read here: \
                     `{name}`."
                ),
                notes,
            ));
        } else if ids.iter().any(|f| outs.contains_key(f)) && !callees.contains(&span) {
            let name = &res.binders[b].name;
            let p = ids.iter().find_map(|f| outs.get(f)).map_or("", |o| o.1);
            errors.push((
                span,
                format!(
                    "`{name}` pushes to its parameter `{p}`, so it is called by name with the \
                     port it writes to, and not used as a value: `{name}`."
                ),
                vec![Note {
                    span,
                    text: format!("repair: call it, as `{name}(…, {p}: m.stdout)`").into(),
                }],
            ));
        }
    }

    // An output port parameter has no default: a call passes the port. A row of a test table
    // gives it by its key and expects what the row pushed there in its value ([`table_rows`]).
    for (&f, &(_, p)) in &outs {
        let decl = t.funcs[&f];
        let name = &res.binders[f].name;
        let ports_at: Vec<(usize, &str)> = (decl.params.iter().enumerate())
            .filter(|(_, q)| {
                t.ids
                    .get(&(q.span, q.name.as_str()))
                    .is_some_and(|b| params.contains(b))
            })
            .map(|(i, q)| (i, q.name.as_str()))
            .collect();
        if let Some(d) = (ports_at.iter()).find_map(|&(i, _)| decl.params[i].default.as_ref()) {
            errors.push((
                d.span,
                format!("An output port has no default: `{p}` of `{name}`, which it pushes to."),
                vec![Note {
                    span: d.span,
                    text: "repair: remove the default, and pass the port at each call".into(),
                }],
            ));
        }
        table_rows(decl, name, &ports_at, &mut errors);
    }
    let writers = outs.into_keys().collect();
    let args = args.iter().map(|a| ((a.call, a.param), a.span)).collect();
    Ports {
        params,
        writers,
        errors,
        not_ports,
        args,
    }
}

/// The errors of the rows of `decl`'s test tables, `decl` the function `name` whose output port
/// parameters are `ports_at`, by place and name. "A port parameter is given by the row's key, as
/// `main`'s ports are; what the row wrote to it is a field of the row's record, named by the
/// parameter: `greet(positional name: Utf8String, out: Lines)` is tested by the row `("a", [])
/// -> { result: (), out: ["hi a"] }`", and "A written port left out of the record is expected
/// to be written nothing" (DESIGN.md sec:ports, "A test table gives a port its values"). So the
/// key's component at a port is `[]`, the port before the row pushes to it, and the value is a
/// record with the field `result` and at most one field per port parameter. A key of another
/// arity is refused where the row is elaborated (`zedc_elab`'s `test_case`), so it is skipped
/// here. The checker's walk then checks each field (`test_args` in walk.rs), and may assume this
/// shape. Cost: one pass over each row's key components and record fields, O(r·(n + f)) for r
/// rows of n parameters and records of f fields; a field is looked up among the n names, so a
/// record costs O(f·n), small since both are written by hand.
fn table_rows(
    decl: &zedc_syntax::ast::Function,
    name: &str,
    ports_at: &[(usize, &str)],
    errors: &mut Vec<(Span, String, Vec<Note>)>,
) {
    let n = decl.params.len();
    let shown: Vec<String> = ports_at.iter().map(|(_, q)| format!("{q}: […]")).collect();
    let record = format!("{{ result: …, {} }}", shown.join(", "));
    for (key, value) in &decl.tests {
        let items: Vec<&Expr> = match &key.kind {
            _ if n == 1 => vec![key],
            ExprKind::Tuple(items) if items.len() == n => items.iter().collect(),
            _ => continue,
        };
        for &(i, q) in ports_at {
            if !matches!(&items[i].kind, ExprKind::Array(xs) if xs.is_empty()) {
                errors.push((
                    items[i].span,
                    format!(
                        "A test key gives the output port `{q}` of `{name}` as `[]`, the port \
                         before the row pushes to it."
                    ),
                    vec![Note {
                        span: items[i].span,
                        text: format!(
                            "repair: write `[]` here, and the lines the row pushes to `{q}` in \
                             its value, as `{record}`"
                        )
                        .into(),
                    }],
                ));
            }
        }
        let ExprKind::Record(fields) = &value.kind else {
            errors.push((
                value.span,
                format!(
                    "A row of `{name}`, which pushes to its parameter `{}`, expects a record: \
                     `{record}`.",
                    ports_at[0].1
                ),
                vec![Note {
                    span: value.span,
                    text: format!(
                        "repair: write the result as the field `result`, and what the row \
                         pushes to each port as the field of its name, a list of lines; a port \
                         left out is expected to be pushed nothing: `{record}`"
                    )
                    .into(),
                }],
            ));
            continue;
        };
        // A field given twice is refused before this, as in any record display.
        for (field, e) in fields {
            if field == "result" || ports_at.iter().any(|&(_, q)| q == field) {
                continue;
            }
            errors.push((
                e.span,
                format!(
                    "`{field}` is not an output port of `{name}`: the record of a row of it has \
                     the fields `result` and {}.",
                    (ports_at.iter())
                        .map(|(_, q)| format!("`{q}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                vec![Note {
                    span: e.span,
                    text: format!("repair: `{record}`").into(),
                }],
            ));
        }
        if !fields.iter().any(|(field, _)| field == "result") {
            errors.push((
                value.span,
                format!("A row of `{name}` gives its result as the field `result`: `{record}`."),
                vec![Note {
                    span: value.span,
                    text: "repair: add the field `result: …`, the value the call gives".into(),
                }],
            ));
        }
    }
}

/// Why an expression statement has no effect ([`silent_tail`]).
#[derive(Debug)]
pub enum Silent<'e> {
    /// This part ends a path that gives a value and writes to no port, so the statement drops
    /// the value.
    Drops(&'e Expr),
    /// No path writes: each one does nothing.
    NoWrite,
}

/// Whether the expression statement whose value is `value` has no effect, and why: the first
/// part, in the order of the text, that ends a path dropping a value, or else, when no path
/// writes, [`Silent::NoWrite`]; none when the statement is legal. DESIGN.md sec:tour_methods:
/// "a call in statement position is legal when it writes a generation (`c*.tick()`) or a port,
/// and dead otherwise", "the check is per flow path: each branch of an `if` or `match` and each
/// block's export is checked on its own", and "a block may export nothing: the empty block
/// `{ }` is a path that does nothing, and a block that exports nothing writes when one of its
/// statements writes or is `break;`. An expression statement is legal when each of its paths
/// writes, breaks or does nothing, and at least one path writes or breaks".
///
/// A path writes when it ends in a call of one of `writers`, the functions with an output port
/// parameter, which every call fills with an output port ([`ports`] rejects any other argument
/// there). The default of an `else` stands in for a failure and is no path of its own, as the
/// repair `c*.m() else #ok;` shows. A statement `if` (`IfStmt`, author P348) comes here as the
/// expression `if` it means: its arms are blocks that export nothing, and a missing `else` is the
/// empty block, which does nothing. A block that exports nothing (the parser allows one only as
/// an arm of a statement `if`, on a path of an expression statement, or ending in `break;`)
/// writes when one of its statements
/// is a push, a `break;` or an expression statement, or a binding whose value writes on some
/// path; otherwise it does nothing. An expression statement in it counts whatever it does, since
/// it is checked on its own, and refused there when it writes on no path: the block's statement
/// is then not refused a second time. No path is claimed to write on every run: a block that
/// leaves early (a `while` or `until` guard, a failure that bubbles out) does nothing on that
/// run, which the rule allows (row SILENT-tail-no-export-safe, which made the old rule, that
/// every path writes, refuse such a block).
// Complexity tradeoff: each node on the paths, and on the paths of the values that a no-export
// block's bindings name, is visited once, from an explicit stack, so the check of one statement
// costs the size of its branches and exports, O(1) for a bare call. A nested expression
// statement is not walked again: it counts as a write, and its own check walks it, so a unit's
// statements cost O(size of the unit) in all, where walking it from each enclosing statement
// would cost O(size x depth). A recursive search costs the same, with the depth of the nest on
// the call stack.
pub fn silent_tail<'e>(
    value: &'e Expr,
    res: &Resolution,
    writers: &HashSet<usize>,
) -> Option<Silent<'e>> {
    // Each part with whether a binding names its value, so that a path ending in it gives the
    // value to the name and drops nothing.
    let mut stack = vec![(value, false)];
    let mut writes = false;
    while let Some((e, named)) = stack.pop() {
        // The parts of a path are pushed last first, so they are met in the order of the text.
        let gives = match &e.kind {
            ExprKind::Call { callee, .. } => {
                let w = matches!(
                    res.uses.get(&callee.span),
                    Some(Ref::Bound(ids)) if ids.iter().any(|f| writers.contains(f))
                );
                writes |= w;
                !w
            }
            ExprKind::If {
                then, otherwise, ..
            } => {
                stack.extend([(&**otherwise, named), (&**then, named)]);
                false
            }
            ExprKind::Else { of, .. } => {
                stack.push((of, named));
                false
            }
            ExprKind::Match { arms, .. } => {
                stack.extend(arms.iter().rev().map(|a| (&a.body, named)));
                false
            }
            ExprKind::Block(stmts) => match stmts.last().map(|s| &s.kind) {
                Some(StmtKind::Return(es)) => match &es[..] {
                    [one] => {
                        stack.push((one, named));
                        false
                    }
                    // A tuple of values is no write, whatever its parts do.
                    _ => true,
                },
                // A block that exports nothing; `{ }` does nothing. Test:
                // `check::ports::tests::a_block_that_exports_nothing_writes_when_a_statement_writes`.
                _ => {
                    for s in stmts.iter().rev() {
                        match &s.kind {
                            StmtKind::Push { .. } | StmtKind::Break | StmtKind::Expr(_) => {
                                writes = true;
                            }
                            StmtKind::Bind { value, .. } => stack.push((value, true)),
                            _ => {}
                        }
                    }
                    false
                }
            },
            _ => true,
        };
        if gives && !named {
            return Some(Silent::Drops(e));
        }
    }
    (!writes).then_some(Silent::NoWrite)
}

/// Whether a parameter of the declared type `ty` is a `Lines` port.
fn is_lines(ty: Option<&TypeKind>) -> bool {
    matches!(ty, Some(TypeKind::Name(n)) if n == "Lines")
}

/// Whether `inner` lies within `outer`.
fn within(inner: Span, outer: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// A binder of the kind `k`, which is no output port, as a message names it.
fn what(k: Kind) -> &'static str {
    match k {
        Kind::Binding => "a binding",
        Kind::Param => "a parameter of a lambda",
        Kind::Function | Kind::Method => "a function",
        Kind::Pattern => "a name a pattern binds",
        Kind::Receiver => "the receiver `this`",
        Kind::Struct | Kind::Type | Kind::TypeParam => "a type",
        Kind::Field => "a field",
        Kind::Unit => "a unit",
        Kind::Port => unreachable!("an output port"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc_syntax::ast::{Stmt, Target};

    fn at(start: usize) -> Span {
        Span {
            start,
            end: start + 1,
        }
    }

    /// The statement `kind` at `start`.
    fn stmt(kind: StmtKind, start: usize) -> Stmt {
        Stmt {
            kind,
            span: at(start),
        }
    }

    /// A call at `start` of the function whose binder is 0, with no arguments.
    fn call(start: usize) -> Expr {
        Expr {
            kind: ExprKind::Call {
                callee: Box::new(Expr {
                    kind: ExprKind::Name("say".into()),
                    span: at(start),
                }),
                positional: Vec::new(),
                named: Vec::new(),
                curry: false,
                infix: false,
            },
            span: at(start),
        }
    }

    /// A block that exports nothing writes when one of its statements is a push, an expression
    /// statement, `break;`, or a binding whose value calls a writer, and otherwise does nothing:
    /// `{ }` and a block of bindings of plain values are statements that write on no path
    /// (DESIGN.md sec:tour_methods, row FAIL-exprstmt-empty-paths). A block that exports a call
    /// of a writer writes, and one that exports a call of no writer drops its value.
    #[test]
    fn a_block_that_exports_nothing_writes_when_a_statement_writes() {
        let mut res = Resolution::default();
        for start in [0, 10, 20] {
            res.uses
                .insert(at(start), Ref::Bound([0].into_iter().collect()));
        }
        let writers: HashSet<usize> = [0].into_iter().collect();
        let block = |stmts: Vec<Stmt>| Expr {
            kind: ExprKind::Block(stmts),
            span: at(100),
        };
        let push = || StmtKind::Push {
            port: "out".into(),
            value: Expr {
                kind: ExprKind::Name("s".into()),
                span: at(30),
            },
        };
        let bind = |value: Expr| StmtKind::Bind {
            targets: vec![Target::Wild],
            value,
        };
        let plain = |start: usize| Expr {
            kind: ExprKind::Bool(true),
            span: at(start),
        };
        for (name, e) in [
            (
                "a call of a writer",
                block(vec![stmt(StmtKind::Expr(call(0)), 0)]),
            ),
            ("a push", block(vec![stmt(push(), 30)])),
            (
                "a call and a push",
                block(vec![stmt(StmtKind::Expr(call(10)), 10), stmt(push(), 30)]),
            ),
            ("a break", block(vec![stmt(StmtKind::Break, 40)])),
            (
                "a binding of a call of a writer",
                block(vec![stmt(bind(call(0)), 0)]),
            ),
        ] {
            let tail = silent_tail(&e, &res, &writers);
            assert!(tail.is_none(), "{name}: {tail:?}");
        }
        for (name, e) in [
            ("nothing", block(Vec::new())),
            (
                "a binding of a plain value",
                block(vec![stmt(bind(plain(50)), 50)]),
            ),
        ] {
            let tail = silent_tail(&e, &res, &writers);
            assert!(matches!(tail, Some(Silent::NoWrite)), "{name}: {tail:?}");
        }
        let exported = block(vec![stmt(StmtKind::Return(vec![call(20)]), 20)]);
        assert!(silent_tail(&exported, &res, &writers).is_none());
        let dropped = block(vec![stmt(StmtKind::Return(vec![plain(60)]), 60)]);
        assert!(matches!(
            silent_tail(&dropped, &res, &writers),
            Some(Silent::Drops(e)) if e.span == at(60)
        ));
    }
}

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
use zedc_resolve::resolve::{Kind, Ref};
use zedc_syntax::ast::{Note, TypeKind};
use zedc_syntax::lex::Span;

/// The output port parameters of a unit and the errors of its uses of output ports.
pub struct Ports {
    /// The binder of each parameter that is an output port.
    pub params: HashSet<usize>,
    /// Each error: its place, its headline and its notes.
    pub errors: Vec<(Span, String, Vec<Note>)>,
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
// resolution once. Test: `l01_19_whole_file_ports::ports::a_chain_of_helpers_passing_a_port_scales`.
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
    for &s in &res.pushes {
        let ids = match res.uses.get(&s) {
            Some(Ref::Bound(ids)) => ids,
            Some(Ref::Prelude(n)) => {
                errors.push((
                    s,
                    format!(
                        "A push goes to an output port, and `{n}` is a prelude word: `{n} <- …;`."
                    ),
                    vec![Note {
                        span: s,
                        text: "repair: push to an output of the program, as `m.stdout <- …;` in \
                               `main`"
                            .into(),
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
                errors.push((
                    s,
                    format!(
                        "A push goes to an output port, and `{name}` is a parameter of `{}` not \
                     declared `Lines`: `{name} <- …;`. Try `{name}: Lines` instead.",
                        res.binders[f].name
                    ),
                    vec![Note {
                        span: p.span,
                        text: format!("the parameter `{name}`"),
                    }],
                ))
            }
            None => errors.push((
                s,
                format!(
                    "A push goes to an output port, and `{name}` is {}: `{name} <- …;`.",
                    what(res.binders[b].kind)
                ),
                vec![Note {
                    span: s,
                    text: "repair: push to an output of the program, as `m.stdout <- …;` in \
                           `main`, or to a parameter declared `Lines` that `main` passes \
                           `m.stdout` to"
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
    for c in &res.calls {
        callees.insert(c.callee);
        let Some(ids) = bound(&c.callee) else {
            continue;
        };
        for &f in ids.iter() {
            let Some(decl) = t.funcs.get(&f) else {
                continue;
            };
            let slots = (c.positional.iter().enumerate())
                .filter_map(|(i, &a)| decl.params.get(i).filter(|p| p.positional).map(|p| (a, p)))
                .chain(c.named.iter().filter_map(|(n, a)| {
                    (decl.params.iter())
                        .find(|p| !p.positional && p.name == *n)
                        .map(|p| (*a, p))
                }));
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
            .filter(|c| !c.contains('\n'))
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
                            ),
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
                            ),
                        },
                        Note {
                            span: a.span,
                            text: format!(
                                "repair: push to `{p}` in `{callee}`, as `{p} <- lines;`, or \
                                 pass `{callee}` the lines to write and push them to `{name}` \
                                 here"
                            ),
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
                    text: format!("`{name}` is pushed to here"),
                }],
                None => Vec::new(),
            };
            let mut notes = notes;
            notes.push(Note {
                span,
                text: format!(
                    "repair: push to `{name}`, as `{name} <- lines;`, or pass it whole to a \
                     parameter that is pushed to"
                ),
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
                    ),
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
                    text: format!("repair: call it, as `{name}(…, {p}: m.stdout)`"),
                }],
            ));
        }
    }

    // An output port parameter has no default and its function no test table: a call passes
    // the port, and a test row gives values only.
    for (&f, &(_, p)) in &outs {
        let decl = t.funcs[&f];
        let name = &res.binders[f].name;
        if let Some(d) = (decl.params.iter())
            .filter(|q| {
                t.ids
                    .get(&(q.span, q.name.as_str()))
                    .is_some_and(|b| params.contains(b))
            })
            .find_map(|q| q.default.as_ref())
        {
            errors.push((
                d.span,
                format!("An output port has no default: `{p}` of `{name}`, which it pushes to."),
                vec![Note {
                    span: d.span,
                    text: "repair: remove the default, and pass the port at each call".into(),
                }],
            ));
        }
        if let Some((row, _)) = decl.tests.first() {
            errors.push((
                row.span,
                format!(
                    "`{name}` pushes to its parameter `{p}`, and a test table gives a function \
                     values, never a port."
                ),
                vec![Note {
                    span: row.span,
                    text: format!(
                        "repair: test a function that computes the lines `{name}` pushes"
                    ),
                }],
            ));
        }
    }
    Ports { params, errors }
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

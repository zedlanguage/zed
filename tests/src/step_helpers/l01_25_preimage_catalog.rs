//! Preimage helpers of step L1.25 (tests/steps/l01_25_preimage_catalog).

use std::sync::Arc;

use zed_kernel::{Shared, Term};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Domains, Preimage};

use super::l01_16_elaboration::{elab, with_prelude};

/// The parameters and the body of the function `ok` that `src` defines, under the
/// interpreter's prelude and the unit's other definitions.
pub fn function(src: &str) -> (Vec<Arc<str>>, Term) {
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let mut t = u.get("ok").expect("a definition `ok`");
    let mut lets = Vec::new();
    while let Term::Let(n, e, b) = &t {
        lets.push((n.clone(), e.clone()));
        t = (**b).clone();
    }
    let Term::Var(k) = &t else {
        panic!("{src}: not a closed definition: {t}")
    };
    let Some(Term::Lam(ps, body)) = lets.iter().find(|(n, _)| n == k).map(|(_, e)| &**e) else {
        panic!("{src}: `{k}` is not a function")
    };
    let body = lets.iter().rev().fold((**body).clone(), |b, (n, e)| {
        Term::Let(n.clone(), e.clone(), Shared::new(b))
    });
    (ps.clone(), with_prelude(body))
}

/// `src` with each parameter written without a type declared `int`, in each definition that
/// starts a line (`name(params) = …` or `name = (params) -> …`), except `main`: a bare
/// literal takes the carrier of its use (DESIGN.md L1.26a), so `ok(x) = x >= 3;` is generic,
/// and its int instance, which rung 2 and the catalog read, is written `ok(x: int) = x >= 3;`.
pub fn int_defs(src: &str) -> String {
    declare_int(src, |_| true)
}

/// [`int_defs`] on the definition of `ok` alone. A parameter declared `int` takes no failure
/// (a failure passed there bubbles out of the call), so a function that passes an argument
/// that may fail to an untyped parameter it does not read, as `g(positional a, positional b)
/// = b` called as `g(x mod n, x)`, keeps its parameters as written.
pub fn int_ok(src: &str) -> String {
    declare_int(src, |name| name == "ok")
}

/// `src` with each parameter written without a type declared `int`, in each definition that
/// starts a line whose name `pick` keeps, except `main`.
fn declare_int(src: &str, pick: impl Fn(&str) -> bool) -> String {
    let mut out = String::with_capacity(src.len() + 16);
    for line in src.split_inclusive('\n') {
        // `name(params) = …` or the lambda form `name = (params) -> …`.
        let head = line.find('(').map(|i| &line[..i]);
        let lambda = head.and_then(|h| h.trim_end().strip_suffix('='));
        let name = (lambda.map(str::trim_end).or(head))
            .filter(|n| n.starts_with(|c: char| c.is_ascii_lowercase()))
            .filter(|n| n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
        let open = name.and(head).map(|h| h.len() + 1);
        let close = open.and_then(|o| line[o..].find(')').map(|c| o + c));
        let (Some(name), Some(open), Some(close)) = (name, open, close) else {
            out.push_str(line);
            continue;
        };
        let after = line[close + 1..].trim_start();
        let defines = if lambda.is_some() {
            after.starts_with("->")
        } else {
            after.starts_with('=') || after.starts_with('{') || after.starts_with("->")
        };
        if name == "main" || !pick(name) || !defines || line[open..close].contains('(') {
            out.push_str(line);
            continue;
        }
        let params: Vec<String> = (line[open..close].split(','))
            .map(|p| match p.trim() {
                p if p.is_empty() || p.contains(':') => p.to_string(),
                p => format!("{p}: int"),
            })
            .collect();
        out.push_str(&line[..open]);
        out.push_str(&params.join(", "));
        out.push_str(&line[close..]);
    }
    out
}

/// The domains `name: [lo..=hi]`, `None` for an unbounded end.
pub fn doms(ds: &[(&str, Option<i64>, Option<i64>)]) -> Domains {
    ds.iter()
        .map(|&(n, lo, hi)| {
            let e = |v: Option<i64>, inf| v.map_or(inf, End::of);
            (
                n.into(),
                IntervalSet::range(e(lo, End::NegInf), e(hi, End::PosInf)),
            )
        })
        .collect()
}

/// The preimage of `true`, printed: each parameter's set, then `exact` or `necessary`, then
/// `enumerated` when it was.
pub fn shown(p: &Preimage) -> String {
    let mut out: Vec<String> = p.domains.iter().map(|(k, v)| format!("{k} {v}")).collect();
    out.push(if p.exact { "exact" } else { "necessary" }.into());
    if p.enumerated {
        out.push("enumerated".into());
    }
    for s in p.stop_texts() {
        out.push(format!("stop: {s}"));
    }
    out.join("; ")
}

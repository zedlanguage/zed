//! Row PRINT-rule1-readback: the six texts PRINT-no-underscore-rest gave its rule 1, each read
//! back and checked against the signature's needs by a check of its own, not by matching the
//! text. Rule 1 (`Sig::uses_written`): a parameter's variable every need of which is an
//! application at fixed arguments (a lookup at a key that holds no variable, or a positional
//! call), and which stands nowhere else, is written as its arrows, one for each distinct
//! application, met by `&`. So the parameter, read back, is a meet of arrows and no variable;
//! there are as many arrows as distinct applications, of the same arities; a lookup's arrow
//! takes the lookup's key; and an arrow's result holds a variable exactly where the need's
//! result is a variable that stands in two places or more, which the printer names (DESIGN.md
//! sec:diagnostics, "Types in a message").

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zedc::check::read::parse_type;
use zedc::check::ty::{Need, NeedKind, Sig, Ty};

use super::scaling::fan;
use super::sig_of;

/// Every signature `s` holds, itself first, each once by address.
fn sigs_in(s: &Arc<Sig>) -> Vec<Arc<Sig>> {
    let mut out: Vec<Arc<Sig>> = Vec::new();
    let mut seen: HashSet<*const Sig> = HashSet::new();
    let mut stack: Vec<Ty> = Vec::new();
    let mut push_sig = |s: &Arc<Sig>, out: &mut Vec<Arc<Sig>>, stack: &mut Vec<Ty>| {
        if seen.insert(Arc::as_ptr(s)) {
            out.push(s.clone());
            for a in &s.arrows {
                stack.extend(a.params.iter().cloned());
                stack.push(a.result.clone());
            }
        }
    };
    push_sig(s, &mut out, &mut stack);
    while let Some(t) = stack.pop() {
        for f in t.fns.iter() {
            push_sig(f, &mut out, &mut stack);
        }
        for r in t.tuples.iter() {
            stack.extend(r.iter().cloned());
        }
    }
    out
}

/// The variables `t` holds at any depth.
fn vars_of(t: &Ty) -> HashSet<Arc<str>> {
    let f = t.var_facts();
    f.names.iter().chain(f.classes.iter()).cloned().collect()
}

/// The arguments of an application at fixed arguments, or `None` for a use of another kind.
fn applied(n: &Need) -> Option<Vec<Ty>> {
    match &n.kind {
        NeedKind::Component { key, .. } | NeedKind::Index { key, .. } => {
            vars_of(key).is_empty().then(|| vec![key.clone()])
        }
        NeedKind::Call {
            positional,
            named,
            curry,
            ..
        } => (named.is_empty() && !curry).then(|| positional.clone()),
        _ => None,
    }
}

/// Checks rule 1 on the signature of `name` in `src`, as the module says, and gives how many
/// parameters it applies to.
fn check_rule_1(src: &str, name: &str) -> usize {
    let s = sig_of(src, name);
    let printed = s.to_string();
    let back = parse_type(&printed).unwrap_or_else(|e| panic!("{src}{printed}: {e}"));
    let back_sig = back
        .fns
        .iter()
        .next()
        .unwrap_or_else(|| panic!("{printed} reads back as no function"))
        .clone();
    let all = sigs_in(&s);
    // The needs of every signature the type holds, each once by its use and application.
    let mut needs: Vec<Need> = Vec::new();
    let mut seen_needs: HashSet<(String, String)> = HashSet::new();
    for g in &all {
        for n in g.decoded_needs_cow().iter() {
            if seen_needs.insert((format!("{:?}", n.span), format!("{:?}", n.kind))) {
                needs.push(n.clone());
            }
        }
    }
    // The places of each variable: each parameter and result of every arrow, and each argument
    // and result of every need, counted once per place.
    let mut places: HashMap<Arc<str>, usize> = HashMap::new();
    let mut count = |t: &Ty| {
        for v in vars_of(t) {
            *places.entry(v).or_default() += 1;
        }
    };
    for a in &s.arrows {
        a.params.iter().for_each(&mut count);
        count(&a.result);
    }
    for n in &needs {
        if let Some(args) = applied(n) {
            args.iter().for_each(&mut count);
        }
        if let Some(r) = &n.result {
            count(r);
        }
    }
    let mut applies = 0;
    for (i, p) in s.arrows[0].params.iter().enumerate() {
        let Some(v) = p.as_var() else { continue };
        let on: Vec<&Need> = needs.iter().filter(|n| n.on.as_var() == Some(v)).collect();
        let Some(apps) = on
            .iter()
            .map(|n| applied(n).map(|a| (a, n.result.clone())))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        // The variable stands nowhere but in its parameter.
        if apps.is_empty() || places.get(v).copied().unwrap_or(0) > 1 {
            continue;
        }
        applies += 1;
        let distinct: Vec<(Vec<Ty>, Option<Ty>)> = {
            let mut d: Vec<(Vec<Ty>, Option<Ty>)> = Vec::new();
            for a in apps {
                if !d.contains(&a) {
                    d.push(a);
                }
            }
            d
        };
        let bp = &back_sig.arrows[0].params[i];
        assert!(
            bp.as_var().is_none() && !bp.dynamic && !bp.fns.is_empty(),
            "{src}{printed}: parameter {i} reads back as no meet of arrows"
        );
        let arrows: Vec<_> = bp.fns.iter().flat_map(|f| f.arrows.clone()).collect();
        assert_eq!(arrows.len(), distinct.len(), "{src}{printed}: arrows");
        let mut want: Vec<(usize, bool)> = distinct
            .iter()
            .map(|(args, r)| {
                let named = r.as_ref().is_some_and(|r| {
                    vars_of(r)
                        .iter()
                        .any(|w| places.get(w).copied().unwrap_or(0) >= 2)
                });
                (args.len(), named)
            })
            .collect();
        let mut got: Vec<(usize, bool)> = arrows
            .iter()
            .map(|a| (a.params.len(), !vars_of(&a.result).is_empty()))
            .collect();
        want.sort_unstable();
        got.sort_unstable();
        assert_eq!(
            got, want,
            "{src}{printed}: (arity, result named) of each arrow"
        );
        // Each lookup's key is the key of one arrow, both ways.
        for (args, _) in &distinct {
            if let [key] = &args[..]
                && vars_of(key).is_empty()
            {
                assert!(
                    arrows.iter().any(|a| a.params.len() == 1
                        && a.params[0].subtype(key)
                        && key.subtype(&a.params[0])),
                    "{src}{printed}: no arrow takes the key {key}"
                );
            }
        }
    }
    applies
}

#[test]
fn a_handled_read_beside_a_component_read_reads_back_as_two_arrows() {
    let k = "k(positional a) = (a[0] else #outOfBounds -> 0) + a[1];\n";
    assert_eq!(check_rule_1(k, "k"), 1);
}

#[test]
fn needs_replayed_through_a_fan_of_calls_read_back_as_one_arrow() {
    assert_eq!(check_rule_1(&fan(3), "g2"), 1);
}

#[test]
fn a_function_called_inside_nested_lambdas_reads_back_as_its_arrow() {
    let g = "g(positional f) = (x) -> (y) -> f(x, y) + x;\n";
    assert_eq!(check_rule_1(g, "g"), 1);
}

#[test]
fn two_functions_called_inside_nested_lambdas_read_back_as_their_arrows() {
    let g = "g(positional f, positional h) = (x) -> (y) -> (h(y, x), f(x), y);\n";
    assert_eq!(check_rule_1(g, "g"), 2);
}

#[test]
fn a_function_called_in_two_lambdas_reads_back_as_a_meet_of_two_arrows() {
    let g = "g(positional f) = ((x) -> f(x), (y) -> (f(y), y));\n";
    assert_eq!(check_rule_1(g, "g"), 1);
}

#[test]
fn a_named_parameter_read_at_a_component_reads_back_as_its_arrow() {
    assert_eq!(check_rule_1("first(p) = p[0];\n", "first"), 1);
}

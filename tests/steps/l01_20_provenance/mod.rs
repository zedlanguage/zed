//! Step L1.20: provenance. A run asked for it records one fact per node instance, at a
//! fact address (static node address, dynamic keypath) no other fact of the run holds, with
//! the facts it read; a failure's origins are the facts where each of its members appeared.

mod kernel;
mod programs;
mod scaling;

use zed_kernel::{Evaluator, Fact, Provenance, Term, Value, World};

/// The value of `t` and the provenance of its run, under wave stamp 0.
pub(crate) fn trace(t: &Term) -> (Value, Provenance) {
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(0)]);
    let v = ev.run(t).unwrap();
    (v, ev.provenance().unwrap())
}

/// Asserts no two facts of `p` share an address.
pub(crate) fn unique(p: &Provenance) {
    let r: Vec<String> = p.repeated().iter().map(|a| a.to_string()).collect();
    assert!(r.is_empty(), "repeated fact addresses: {r:?}");
    assert!(p.facts().len() > 1);
}

/// The facts at the node whose term prints as `text`.
pub(crate) fn at<'a>(p: &'a Provenance, text: &str) -> Vec<&'a Fact> {
    let terms = p.terms();
    p.facts()
        .iter()
        .filter(|f| terms[f.address.node.position() as usize].to_string() == text)
        .collect()
}

/// The terms of the origins of fact `i`'s failure, printed, with the value each produced.
pub(crate) fn origins(p: &Provenance, i: usize) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = p
        .origins(i)
        .into_iter()
        .map(|j| {
            let f = &p.facts()[j];
            let v = f.value.as_ref().map_or("<fn>".into(), Value::to_string);
            (p.term(&f.address.node).to_string(), v)
        })
        .collect();
    out.sort();
    out
}

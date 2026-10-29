//! Step M0.7: the canonicalizer (DESIGN.md sec:ir, "Identity"). Definitions from ordinary
//! programs (an invoice total, a running balance, a status-code check) written with different
//! local names, facets in different orders, and domains spelled differently, and the content
//! addresses they get.

mod alpha;
mod domains;
mod rules;

use std::sync::Arc;

use zed_kernel::term::Term;
use zedc::address::ContentAddress;
use zedc::canon::{Def, Facet, address};

/// No definition resolves: every free variable is hashed by name.
fn none(_: &str) -> Option<ContentAddress> {
    None
}

/// The definition `name = body` with no domain and no facets.
fn def(name: &str, body: Term) -> Def {
    Def {
        name: name.into(),
        domain: None,
        facets: vec![],
        body,
    }
}

/// A facet that is not a hint.
fn facet(kind: &str, value: impl Into<zed_kernel::value::Value>) -> Facet {
    Facet {
        hint: false,
        kind: Arc::from(kind),
        value: value.into(),
    }
}

fn addr(d: &Def) -> ContentAddress {
    address(d, &none)
}

//! A definition as the canonicalizer sees it, and its facets: the input of every rule of
//! [`super::RULES`] and of the serialization (`serial`), kept in a file below both.

use std::sync::Arc;

use zed_kernel::term::Term;
use zed_kernel::value::Value;

use super::domain::Domain;

/// A facet of a definition: a named fact about it, such as its units or a proved property.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Facet {
    /// Whether the facet is a hint, which diagnostics and printing read and no value may
    /// depend on, such as a binder's written name.
    pub hint: bool,
    /// The facet's kind, such as `units`.
    pub kind: Arc<str>,
    /// The facet's value.
    pub value: Value,
}

/// A definition as the canonicalizer sees it.
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    /// The declaration's own name, which is part of its interface and so of its value.
    pub name: Arc<str>,
    /// The integer facts of its result, when it has any.
    pub domain: Option<Domain>,
    /// Its other facets.
    pub facets: Vec<Facet>,
    /// Its body.
    pub body: Term,
}

//! What elaboration gives: a unit's definitions and the cases of its `test` tables, which the
//! stager, the runner and the queries read below elaboration.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::{Shared, Term};

use zedc_syntax::ast::Error;
use zedc_syntax::lex::Span;

/// A top-level definition.
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    /// Its source name, or the temporary's name for the tuple of `a, b = e;`.
    pub name: String,
    /// Its kernel name.
    pub kernel: Arc<str>,
    /// Its value, shared with the lets that close a term over it.
    pub term: Shared,
    /// Whether it is bound by `=` to a value whose type, as the checker gives it, has no
    /// function component (step L1.37).
    pub first_order: bool,
}

/// A case of a `test` table: `f(input) == expected`.
#[derive(Clone, Debug, PartialEq)]
pub struct Test {
    /// The function's source name.
    pub function: String,
    /// The function's kernel name, unique in the unit.
    pub kernel: Arc<str>,
    /// The bool term that checks the case, over the unit's definitions.
    pub check: Term,
    /// The arguments the key gives, in declaration order; for a row of `main`, the inputs its
    /// key gives, then the values its table's clause `test with p = e, …` gives, by `ports`.
    pub args: Vec<Term>,
    /// For a row of `main`, the field of `MainArgs` each of the last `ports.len()` of `args`
    /// gives, written as `zedc_elab::MAIN_KEY` writes it; empty for any other row.
    pub ports: Vec<&'static str>,
    /// The expected value.
    pub want: Term,
    /// The case's text.
    pub span: Span,
}

/// An elaborated unit.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Unit {
    /// The definitions, each after those it uses.
    pub defs: Vec<Def>,
    /// The test cases, in written order, shared with the unit once staged.
    pub tests: Arc<[Test]>,
    /// The warnings, which do not stop the build: each operation that widens a value past a
    /// machine word (DESIGN.md sec:domains). `front::compile` moves them out, placed in the
    /// source, and leaves this empty.
    pub warnings: Vec<Error>,
    /// For each declared function, by its kernel name, whether each parameter takes only `int`s
    /// on every arrow the checker gives it (`Sig::int_params`): the parameters rung 2 may read
    /// as integers (RUNG2-carrier). `front::linear_questions` reads them; a mixed unit, which
    /// nothing asks a question of, leaves this empty.
    pub int_params: HashMap<Arc<str>, Vec<bool>>,
}

/// The name the program wrote for the binder whose kernel name is `kernel`: the kernel name
/// itself, or the part before `@k` where elaboration renamed the binder (`Elab::new`). A
/// written name holds no `@` (`crate::lex::name`), and neither does a temporary `$k`, which
/// is kept as it is. A message names a binder by it (sec:diagnostics). Linear in the length
/// of the name.
pub fn written_name(kernel: &str) -> &str {
    kernel
        .split_once('@')
        .map_or(kernel, |(written, _)| written)
}

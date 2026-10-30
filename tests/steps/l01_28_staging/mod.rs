//! Step L1.28: staging. A term is build-stage when it reads only build-stage definitions and
//! prelude words and no port; the build evaluates the demanded ones to literals, leaves the
//! rest to run, never evaluates a definition nothing reads, and leaves a build-stage term
//! whose evaluation fails or runs out of fuel to run whole. The Trick specializes a function
//! on a parameter only when the parameter's domain is finite and small.

mod mix;
mod scaling;
mod trick;

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Lookup;
use zedc::run::{Program, load};
use zedc::stage::Report;

/// The program `src`, and it staged under `fuel`, with the report.
pub(crate) fn staged(src: &str, fuel: u64) -> (Program, Program, Report) {
    let p = load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}: {e}"));
    let (s, report) = p.stage(fuel);
    (p, s, report)
}

/// What one wave of `p` writes to `stdout` on `stdin`, or its error.
pub(crate) fn out(p: &Program, stdin: &str) -> String {
    let mut lines = BTreeMap::new();
    lines.insert("stdin".to_string(), stdin.as_bytes().to_vec());
    let files = |_: &str| -> Arc<dyn Lookup> { unreachable!("no `Files` port") };
    match p.run(&lines, files) {
        Ok(w) => w
            .writes
            .iter()
            .map(|(_, b)| String::from_utf8_lossy(b).into_owned())
            .collect(),
        Err(e) => format!("error: {e}"),
    }
}

/// The term of definition `name` of `p`, printed.
pub(crate) fn term(p: &Program, name: &str) -> String {
    let d = p.unit().defs.iter().find(|d| d.name == name);
    d.unwrap_or_else(|| panic!("no definition `{name}`"))
        .term
        .to_string()
}

//! Grammar-tool helpers of step M0.3 (tests/steps/m0_03_grammar_tools).

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;
use std::sync::{Mutex, PoisonError};

use zed_tools::Outcome;

/// A directory under `build/` that is removed at the end of the test.
pub struct Dir(pub PathBuf);

/// The names `Dir::new` has given in this process. Two tests that used one name deleted each
/// other's files when they ran at once, which failed one or both only now and then
/// (TEST-m0_03-flake: two tests of m0_03 shared `fuzz_real`); a second use now fails at once.
static NAMES: Mutex<BTreeSet<String>> = Mutex::new(BTreeSet::new());

impl Dir {
    /// A new empty directory named `name`, a name no other `Dir` of this test binary has. It
    /// lies in a directory named after the binary, so the binaries running at once that use
    /// these helpers do not share one either.
    pub fn new(name: &str) -> Dir {
        let fresh = NAMES
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(name.to_string());
        assert!(fresh, "two tests use the test directory {name}");
        let exe = std::env::current_exe().expect("the test binary's path");
        let stem = exe
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("a UTF-8 name");
        // Cargo names a test binary `<target>-<hash>`.
        let binary = stem.rsplit_once('-').map_or(stem, |(b, _)| b);
        let path = PathBuf::from(format!(
            "{}/build/tool_tests/{binary}/{name}",
            zed_tools::impl_root()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).expect("removing an earlier run's directory");
        }
        fs::create_dir_all(&path).expect("creating a test directory");
        Dir(path)
    }

    /// The path of `name` in this directory.
    pub fn at(&self, name: &str) -> String {
        self.0.join(name).to_str().expect("UTF-8 path").into()
    }

    /// Writes `text` to `name` in this directory and gives its path.
    pub fn write(&self, name: &str, text: &str) -> String {
        let path = self.at(name);
        fs::write(&path, text).expect("writing a test file");
        path
    }

    /// This directory's path.
    pub fn root(&self) -> String {
        self.0.to_str().expect("UTF-8 path").into()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        // A test that has failed still removes its directory, so this cannot be allowed to panic.
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// The copy of a grammar file in `zed/grammar`.
pub fn grammar(name: &str) -> String {
    fs::read_to_string(format!("{}/zed/grammar/{name}", zed_tools::impl_root()))
        .expect("a file of zed/grammar")
}

/// A table with `sorted` at L3 and the `log` port at L7.
const WORDS: &str = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
                     | L1 | | | `len` |\n| L3 | | | `sorted` |\n| L7 | | | `log` |\n";

/// The text of a `DESIGN.md` with the given grammars, then `body`.
pub fn design_of(lex: &str, syn: &str, doc: &str, desugar: &str, body: &str) -> String {
    format!(
        "# Test spec\n\n{WORDS}\n```peg\n{lex}```\n\n```peg\n{syn}```\n\n```peg\n{doc}```\n\n\
         ```desugar\n{desugar}```\n\n{body}\n"
    )
}

/// A `DESIGN.md` with the real grammars, then `body`.
pub fn design(body: &str) -> String {
    design_of(
        &grammar("lexical.peg"),
        &grammar("syntax.peg"),
        &grammar("notation.peg"),
        &grammar("desugar.txt"),
        body,
    )
}

/// A ```` ```zed ```` fence.
pub fn fence(text: &str) -> String {
    format!("```zed\n{text}\n```\n")
}

/// A spec whose `DESIGN.md` is `design` and whose `EXAMPLES.md` is `examples`.
pub fn spec_dir(name: &str, design: &str, examples: &str) -> Dir {
    let dir = Dir::new(name);
    dir.write("DESIGN.md", design);
    dir.write("EXAMPLES.md", examples);
    dir
}

/// Runs a tool and gives what it printed.
pub fn tool(run: fn(&[String], &mut String) -> Outcome, args: &[&str]) -> (Outcome, String) {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    let mut out = String::new();
    let outcome = run(&args, &mut out);
    (outcome, out)
}

/// The kernel grammar of a test spec: seven generators, so `sync` can list the words no message
/// prints (`zed_tools::spec_checks::kernel_rules`). A spec `sync` copies must have one.
pub const KERNEL: &str = "# (sec:kernel) Kernel\n\n```\nF ::= fam(D, i -> e)\n    | reindex(F, kf, vf)\n    \
                          | discard(F, sel)\n    | fold(F, op, ev)\n    | fix(F0, step, ev)\n    \
                          | gen(init, step, guard)\n    | port(decl)\n```\n";

/// A directory standing for `zed/` with its two subdirectories, for `sync` to write.
pub fn zed_dir(name: &str) -> Dir {
    let zed = Dir::new(name);
    for sub in ["fences", "grammar"] {
        fs::create_dir(zed.at(sub)).expect("a copy directory");
    }
    zed
}

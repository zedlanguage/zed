//! FAIL-values-function-in-payload-run, found by fix-values (2026-11-14) while working on
//! FAIL-values-function-in-tuple. The checker accepts an atom whose payload holds a function
//! (DESIGN.md L1.17 and `#atom(t)`: a payload may hold a function; test
//! `completeness::building_an_atom_that_holds_a_function_is_no_error` in l01_17), but the run
//! stops with "a bug in zedc itself ... `#box(..)` applied to a function": the kernel's
//! `Prim::Atom` (crates/zed-kernel/src/eval.rs, the loop that collects `V::Data` arguments
//! before `prim_data`) takes data only, and so do the counting machine
//! (crates/zedc-zir/src/zir/memory.rs, `Op::Prim(Prim::Atom) if ins.iter().all(data)`) and
//! native code (crates/zed-native/src/hooks.rs). DESIGN L1.17: "Every type error this step
//! names is one the checker rejects before the program runs".
//!
//! To use this file: drop it into tests/steps/l01_17_value_representation/ as a module
//! (`mod function_in_payload_run;` in its mod.rs).

use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// A payload that holds a function, passed through a function so the atom is built at run
/// time, then passed over by an `else` that names another atom.
#[test]
fn an_atom_whose_payload_holds_a_function_runs() {
    let src = "f(positional v: int) = v + 1;\ng(positional a) = a;\nmain(m: MainArgs) {\n  x = \
               g(#box(f));\n  m.stdout <- (x else #nope -> \"no\") else \"box\";\n}\n";
    let out = run("function_in_payload_run", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "box\n"),
        "{}",
        out.stderr
    );
}

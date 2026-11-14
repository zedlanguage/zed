//! The target values of the `layer` tool (FAIL-layer-mcu-target-value, found by
//! TEST-complete-crates, author P189). DESIGN.md sec:layers, "Defined words by layer": "a target
//! value (`#cpu`, `#wasm`, `#gpu`, `#cluster`, `#mcu`) is one only as the argument of `target(…)`
//! or of `@require`'s `target:`, elsewhere an ordinary atom", and the table lists "the target
//! value `#mcu`" at L31. The tool knew four of the five (`TARGET_ATOMS` in
//! crates/zed-tools/src/layer.rs), so `#mcu` in a type or a pattern counted as an atom read of
//! layer L31, where `#cpu` in the same place counts as nothing.

use super::{Dir, grammar, tool};
use zed_tools::layer;

/// A spec whose DESIGN.md table lists `words`, each at its own layer.
fn spec(name: &str, words: &[(u32, &str)]) -> Dir {
    let rows: String = words
        .iter()
        .map(|(k, w)| format!("| L{k} | — | — | `{w}` |\n"))
        .collect();
    let table = format!("| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n{rows}");
    let design = format!(
        "# Test spec\n\n{table}\n```peg\n{}```\n\n```peg\n{}```\n\n```peg\n{}```\n\n\
         ```desugar\n{}```\n",
        grammar("lexical.peg"),
        grammar("syntax.peg"),
        grammar("notation.peg"),
        grammar("desugar.txt"),
    );
    let dir = Dir::new(name);
    dir.write("DESIGN.md", &design);
    dir.write("EXAMPLES.md", "");
    dir
}

/// The hits `layer -v` lists for `program`, as `L<k> <word> <how>`.
fn hits(dir: &Dir, file: &str, program: &str) -> Vec<String> {
    let path = dir.write(file, program);
    let (outcome, out) = tool(layer::run, &[&dir.root(), "-v", &path]);
    assert!(outcome.is_ok(), "{program}\n{outcome:?}\n{out}");
    out.lines()
        .filter(|l| l.starts_with("      L"))
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
fn mcu_is_a_target_value_like_cpu() {
    let dir = spec("mcu_target_value", &[(9, "#cpu"), (31, "#mcu")]);
    for (i, atom) in ["#cpu", "#mcu"].into_iter().enumerate() {
        // Outside `target(…)` a target value is an ordinary atom: no hit.
        let program = format!("// layer L1\nf(x: {atom} | int) -> int = 1;\n");
        assert_eq!(
            hits(&dir, &format!("t{i}.zed"), &program),
            Vec::<String>::new(),
            "{atom}"
        );
        // Inside `@require(target: …)` it is a target value.
        let program = format!("// layer L1\n@require(target: {atom})\nf() -> int = 1;\n");
        let got = hits(&dir, &format!("r{i}.zed"), &program);
        assert_eq!(got.len(), 1, "{atom}: {got:?}");
        assert!(
            got[0].ends_with(&format!("{atom} target value")),
            "{atom}: {got:?}"
        );
    }
}

/// Each of the five target values DESIGN lists counts as nothing in a type, a pattern and an
/// expression, and as a target value in `@require(target: …)` and `with target(…)`; an atom
/// that is not a target value counts as an atom read in a type.
#[test]
fn each_target_value_counts_only_as_the_argument_of_target() {
    let values = [
        (9, "#cpu"),
        (24, "#wasm"),
        (26, "#gpu"),
        (27, "#cluster"),
        (31, "#mcu"),
    ];
    let mut words = values.to_vec();
    words.push((8, "#lost"));
    let dir = spec("each_target_value", &words);
    for (i, (k, atom)) in values.into_iter().enumerate() {
        let outside = [
            format!("f(x: {atom} | int) -> int = 1;\n"),
            format!("f(x: {atom} | int) -> int = match x {{ {atom} -> 0, _ -> 1 }};\n"),
            format!("f() -> {atom} = {atom};\n"),
        ];
        for (j, program) in outside.iter().enumerate() {
            let got = hits(
                &dir,
                &format!("o{i}_{j}.zed"),
                &format!("// layer L1\n{program}"),
            );
            assert_eq!(got, Vec::<String>::new(), "{program}");
        }
        let program = format!("// layer L1\n@require(target: {atom})\nf() -> int = 1;\n");
        let got = hits(&dir, &format!("r{i}.zed"), &program);
        assert_eq!(got, [format!("L{k} {atom} target value")], "{program}");
        let program = format!("// layer L1\nf(x: int) -> int = x with target({atom});\n");
        let got = hits(&dir, &format!("w{i}.zed"), &program);
        assert!(
            got.contains(&format!("L{k} {atom} target value")),
            "{program}: {got:?}"
        );
    }
    let program = "// layer L1\nf(x: #lost | int) -> int = 1;\n";
    assert_eq!(hits(&dir, "lost.zed", program), ["L8 #lost atom read"]);
}

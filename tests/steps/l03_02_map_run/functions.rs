//! A family whose entries hold functions, read and applied, run by `zedc run` and by an
//! executable `zedc build` makes (row FAIL-family-function-entry; DESIGN.md
//! sec:values_morphisms, "Application is indexing"). The reference evaluator's values of the
//! same programs are in `l01_17_value_representation::function_in_family`; each expected line
//! is worked by hand. A `map` whose result holds a function runs in an executable too: the
//! executable runs a `fam` node in the kernel, which gives the family of functions back as a
//! held value (row FAIL-native-fam-result-holds-function).

use zed_tests::step_helpers::l01_36a_executables::{Ran, built, dir, executable, interpreter};

/// `b["a"](n)` is `n + 1` and `b["b"](n)` is `2 n`; `ka`, `kb` and `kz` name the keys, `kz`
/// one that is not in `b`.
const B: &str = "    b = { \"a\" -> (y -> y + 1), \"b\" -> (y -> y * 2) };\n    ka = \"a\";\n    \
                 kb = \"b\";\n    ks = [\"a\", \"z\"];\n    kz = ks[1];\n";

/// The program `name`, the declarations `top` and then a `main` that runs `B` and then `body`,
/// run by `zedc run` and by the executable `zedc build` makes of it.
fn both(name: &str, top: &str, body: &str) -> [Ran; 2] {
    let d = dir(&format!("l03_02_map_run/{name}"));
    let src = d.join(format!("{name}.zed"));
    std::fs::write(&src, format!("{top}main(m: MainArgs) {{\n{B}{body}}}\n")).unwrap();
    let exe = d.join(name);
    built(&src, &exe);
    [interpreter(&src, &[], &[]), executable(&exe, &[], &[])]
}

/// Each line, `r = …;` then a write of `r`, with the line the program must write.
#[test]
fn entries_that_are_functions_are_read_and_applied() {
    // Each case binds its value to `r` and may use `c`; case `i` renames them `ri` and `ci`.
    let cases = [
        ("r = b[ka](2);", "3"),
        ("r = b[kb](2);", "4"),
        ("r = ap(b, kb);", "20"),
        ("c = (b, 1);\n    r = c[0][ka](2);", "3"),
        ("r = [b, b][1][kb](3);", "6"),
        ("c = { 1 -> b, 2 -> b };\n    r = c[2][kb](3);", "6"),
        (
            "c = { ka -> { kb -> (y -> y + 1) } };\n    r = c[ka][kb](2);",
            "3",
        ),
        ("r = [(x -> x + 1), (x -> x * 2)][1](5);", "10"),
        ("r = b[kz](2) else #notFound -> -1;", "-1"),
        ("r = b[ka](2);", "3"),
        ("r = (b[kz] else #notFound -> (y -> 0))(5);", "0"),
        ("r = (b[ka])(5);", "6"),
        ("r = b.count;", "2"),
        ("r = ka in b;", "true"),
        ("r = kz in b;", "false"),
        ("c = b.first;\n    r = c(4);", "5"),
        ("c = b.last;\n    r = c(4);", "8"),
        (
            "c = { ka -> (y -> y + 1), kb -> 7 };\n    r = c.count;",
            "2",
        ),
        ("r = b.map(f -> f(2));", "{\"a\" -> 3, \"b\" -> 4}"),
        // `where` and a remap keep the functions (row FAIL-held-family-operators).
        ("r = b.where(f -> true).count;", "2"),
        ("c = b.where(f -> true);\n    r = c[ka](2);", "3"),
        ("r = b.where(f -> f(3) > 5).count;", "1"),
        ("c = b.where(f -> f(3) > 5);\n    r = c[kb](3);", "6"),
        ("c = b as (k -> v) into (k -> v);\n    r = c[ka](2);", "3"),
    ];
    let body: String = (cases.iter().enumerate())
        .map(|(i, (c, _))| {
            let c = c
                .replace("c = ", &format!("c{i} = "))
                .replace("c[", &format!("c{i}["));
            let c = c
                .replace("c(", &format!("c{i}("))
                .replace("c.", &format!("c{i}."));
            let c = c.replace("r = ", &format!("r{i} = "));
            format!("    {c}\n")
        })
        .collect();
    // A run pushes to `m.stdout` once: one line per case.
    let lines: Vec<String> = (0..cases.len()).map(|i| format!("\"${{r{i}}}\"")).collect();
    let body = format!("{body}    m.stdout <- [{}];\n", lines.join(", "));
    let want: String = cases.iter().map(|(_, w)| format!("{w}\n")).collect();
    let top = "ap(positional f, positional k) = f[k](10);\n";
    for (how, ran) in ["zedc run", "executable"]
        .iter()
        .zip(both("entries", top, &body))
    {
        assert_eq!(
            (ran.status, ran.stdout.as_str()),
            (0, want.as_str()),
            "{how}: {}",
            ran.stderr
        );
    }
}

/// Two function entries at one key: the run stops with the collision of sec:corner_cases, as
/// a display of data does, and not as a bug in zedc.
#[test]
fn two_function_entries_at_one_key_collide() {
    let body = "    c = { ka -> (y -> y + 1), ka -> (y -> y) };\n    r = c[ka](1);\n    \
                m.stdout <- \"${r}\";\n";
    for (how, ran) in ["zedc run", "executable"]
        .iter()
        .zip(both("collide", "", body))
    {
        assert!(
            ran.status != 0
                && ran.stdout.is_empty()
                && ran
                    .stderr
                    .contains("two entries were written at the same key path, [\"a\"]")
                && !ran.stderr.contains("a bug in zedc"),
            "{how}: {} {:?} {}",
            ran.status,
            ran.stdout,
            ran.stderr
        );
    }
}

/// A `map` that makes functions: 2 + 1, and f(1) + 100 at "b" (row
/// FAIL-native-fam-result-holds-function: the executable runs the `map` in the kernel, which
/// gives the family of functions back as a held value).
#[test]
fn a_map_that_makes_functions_runs_in_both() {
    let body = "    c = { ka -> 1 }.map(r -> (y -> y + r));\n    r = c[ka](2);\n    \
                d = b.map(f -> (y -> f(y) + 100));\n    s = d[kb](1);\n    \
                m.stdout <- \"${r} ${s}\";\n";
    for (how, ran) in ["zedc run", "executable"]
        .iter()
        .zip(both("made_both", "", body))
    {
        assert_eq!(
            (ran.status, ran.stdout.as_str()),
            (0, "3 102\n"),
            "{how}: {}",
            ran.stderr
        );
    }
}

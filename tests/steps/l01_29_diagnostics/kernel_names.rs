//! A message names a binder as the user wrote it (item NAME-at-print, DESIGN.md "Printed types
//! are syntax"). Elaboration renames a binder `x` to `x@k` when another binder of the unit is
//! named `x` too, or when it is named like a prelude word; no message shows that name, which
//! the user cannot write, and a message about one function does not change with the names
//! the other functions of its unit use.

use super::rejected;

/// The first kernel name `x@k` in the messages of `out`, the lines that show the source left
/// out: a name, `@`, a digit. A written name holds no `@` (`zedc::lex::name`).
pub(super) fn kernel_name(out: &str) -> Option<&str> {
    let shows_source = |l: &str| {
        let t = l.trim_start();
        t.starts_with('|')
            || t.split_once(" | ")
                .is_some_and(|(n, _)| n.parse::<u32>().is_ok())
    };
    out.lines().filter(|l| !shows_source(l)).find_map(|l| {
        l.match_indices('@').find_map(|(i, _)| {
            let start = l[..i]
                .rfind(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
                .map_or(0, |j| j + 1);
            let digits = l[i + 1..].len()
                - l[i + 1..]
                    .trim_start_matches(|c: char| c.is_ascii_digit())
                    .len();
            (start < i && digits > 0).then(|| &l[start..i + 1 + digits])
        })
    })
}

/// `ok` over `x, y, z, w`, a cycle `3 * next - this >= 10` whose question the solver refuses
/// (l01_38_presburger::checker, "tie"), with its parameters named by `names`. They are
/// declared `int`, since the question is asked only of a function whose parameters take only
/// `int`s, and bare literals leave the carrier open.
fn tie(names: [&str; 4]) -> String {
    let [x, y, z, w] = names;
    format!(
        "ok({x}: int, {y}: int, {z}: int, {w}: int) = 3 * {y} - {x} - 10 >= 0 && 3 * {z} - {y} \
         - 10 >= 0 && 3 * {w} - {z} - 10 >= 0 && 3 * {x} - {w} - 10 >= 0;\n"
    )
}

/// A unit of `defs` whose `main` calls `ok` at `args`.
fn calling(defs: &str, args: &str) -> String {
    format!(
        "{defs}main(m: MainArgs) {{\n  a = int(m.stdin[1] else \"0\") else 0;\n  \
         r = if ok({args}) {{ \"in\" }} else {{ \"out\" }};\n  m.stdout <- \"${{r}}\";\n}}\n"
    )
}

#[test]
fn the_kernel_name_finder_finds_one_and_skips_the_source() {
    assert_eq!(kernel_name("1:1: `x@2` is wrong"), Some("x@2"));
    assert_eq!(
        kernel_name("1:1: rows `-w + 3 * min@14 - 10`"),
        Some("min@14")
    );
    assert_eq!(kernel_name("1:1: mail a@b or @3 or x@"), None);
    assert_eq!(kernel_name("  2 | s = \"x@2\";\n    |     ^"), None);
}

#[test]
fn a_refused_question_names_the_parameters_as_written_when_another_function_shares_them() {
    let alone = calling(&tie(["x", "y", "z", "w"]), "x: a, y: a, z: a, w: a");
    let shared = calling(
        &format!("{}other(x, y) = x > y;\n", tie(["x", "y", "z", "w"])),
        "x: a, y: a, z: a, w: a",
    );
    let (alone, shared) = (rejected(&alone), rejected(&shared));
    assert_eq!(kernel_name(&shared), None, "{shared}");
    assert!(
        shared.contains("the constraints: x <= 3 * y - 10"),
        "{shared}"
    );
    // The message, without the address that hashes the whole unit, is that of `ok` alone.
    let messages = |out: &str| -> Vec<String> {
        (out.lines())
            .filter(|l| !l.trim_start().starts_with("address:"))
            .map(str::to_owned)
            .collect()
    };
    assert_eq!(messages(&shared), messages(&alone));
}

#[test]
fn a_parameter_named_like_a_prelude_word_is_named_as_written() {
    let out = rejected(&calling(
        &tie(["min", "len", "abs", "w"]),
        "min: a, len: a, abs: a, w: a",
    ));
    assert_eq!(kernel_name(&out), None, "{out}");
    assert!(
        out.contains("the constraints: 3 * len >= min + 10"),
        "{out}"
    );
}

#[test]
fn a_division_the_constraints_define_names_its_operand_as_written() {
    let ok = "ok(x, y, z, w) = 4 * (x div 3) - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 \
              * x - 10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w \
              - 5 * x + 12 * y - z + 31 >= 0;\nother(x) = x > 2;\n";
    let out = rejected(&calling(ok, "x: a, y: a, z: a, w: a"));
    assert_eq!(kernel_name(&out), None, "{out}");
    assert!(out.contains("where q0 = x div 3"), "{out}");
}

#[test]
fn each_overload_asks_its_own_question() {
    // `ok` over four names is refused at its own line; the overload `ok(x)` after it, over a
    // decided question, asks its own and is not asked the other's.
    let src = format!(
        "{}ok(x) = x > 2;\nmain(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n",
        tie(["x", "y", "z", "w"])
    );
    let out = rejected(&src);
    assert_eq!(kernel_name(&out), None, "{out}");
    let firsts: Vec<&str> = (out.lines())
        .filter(|l| l.contains("zedc could not decide whether"))
        .collect();
    assert_eq!(firsts.len(), 1, "{out}");
    assert!(
        firsts[0].starts_with("1:1: zedc could not decide whether the condition of `ok`,"),
        "{out}"
    );
}

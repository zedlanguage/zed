//! Every command of the zedc executable that reads a program prints a rejection of it in full,
//! as a user runs it (item FIX-fmt-parse-notes, DESIGN.md sec:diagnostics): the message at its
//! line and column, each step of its derivation with the source line it stands on, and each
//! repair. `zedc run`, `zedc replay`, `zedc build` and `zedc fmt` print it alike on standard
//! error; `zedc test` prints it in its report on standard output, followed by the count of
//! passed and failed checks. `zedc fmt` reads the syntax of a file only, so a program whose
//! syntax is accepted and whose types are not is printed in layout by `zedc fmt` and rejected by
//! the others. `crates/zed-native/Cargo.toml` names this test, since only a test of that package
//! can name the executable.
#![cfg(target_os = "linux")]

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// A loop whose boundary item has neither `initial` nor an index: a parse error with three
/// steps, its statement, its loop and its repair.
const BARE: &str = "f(n) = loop t {\n  while t < n;\n  x' = x + 1 with x = 0;\n};\n";

/// What every command prints for [`BARE`] in the file `file`, without the final line break.
fn bare_rejection(file: &Path) -> String {
    format!(
        "{}:3:19: `with x = 0` stands on `x' = x + 1 with x = 0;` in the body of a `loop`, \
         and it gives `x` no sentinel value: without `initial` or a key, it reads as though `x` \
         took the value `0` anew on every step. The sentinel value of `x`, its value before \
         step 0, is given once, by a statement of its own, `initial x = 0;`, which may stand \
         anywhere among the statements of the loop's body.\n  \
         [1] 3:3: the statement the `with` clause stands on\n      \
         3 |   x' = x + 1 with x = 0;\n        \
         |   ^^^^^^^^^^^^^^^^^^^^^^ [1]\n        \
         |                   ^^^^^ [3]\n  \
         [2] 1:8: the loop whose body holds the statement\n      \
         1 | f(n) = loop t {{\n        \
         |        ^^^^\n  \
         [3] 3:19: repair: `initial x = 0; x' = x + 1;`, `initial x = 0;` written beside the \
         statement, the sentinel value given once, before step 0, and the `with` clause deleted",
        file.display()
    )
}

/// The file `name` in this test's directory under the test target's scratch directory, holding
/// `text`; it is overwritten by each run, never deleted.
fn file(name: &str, text: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("l01_29_commands_binary");
    std::fs::create_dir_all(&d).unwrap();
    let f = d.join(name);
    std::fs::write(&f, text).unwrap();
    f
}

/// The runtime library built with `zedc`, which `zedc build` checks before it reads the
/// program, as `tests/steps/l01_36a_executables/binary.rs` finds it.
fn runtime() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    zed_native::link::runtime_of(Path::new(env!("CARGO_BIN_EXE_zedc")), exe.parent().unwrap())
        .unwrap_or_else(|e| panic!("{e}"))
}

/// `zedc <command> <file> <after>` with no input, the runtime library and linker of `zedc build`
/// named: status, stdout and stderr.
fn zedc(command: &str, file: &Path, after: &[&str]) -> (Option<i32>, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_zedc"))
        .arg(command)
        .arg(file)
        .args(after)
        .env("ZED_RUNTIME", runtime())
        .env("CC", "cc")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    (
        out.status.code(),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

/// The words after the file that `command` needs to reach the program: `zedc replay` names a
/// record, which it reads only after the program is accepted, and `zedc build` an output.
fn after(command: &str, out: &Path) -> Vec<String> {
    match command {
        "replay" => vec![out.with_extension("record").display().to_string()],
        "build" => vec!["-o".into(), out.display().to_string()],
        _ => Vec::new(),
    }
}

/// What `command` prints for the file `f` when it rejects it: standard error with status 1 and
/// nothing on standard output, or, for `zedc test`, its report on standard output.
fn rejection(command: &str, f: &Path) -> String {
    let words = after(command, &f.with_extension(format!("{command}.out")));
    let words: Vec<&str> = words.iter().map(String::as_str).collect();
    let (status, out, err) = zedc(command, f, &words);
    assert_eq!(
        status,
        Some(1),
        "zedc {command} {}: {out}{err}",
        f.display()
    );
    if command == "test" {
        assert_eq!(err, "", "zedc test {}", f.display());
        return out;
    }
    assert_eq!(out, "", "zedc {command} {}: {err}", f.display());
    err
}

#[test]
fn zedc_fmt_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("fmt.zed", BARE);
    assert_eq!(rejection("fmt", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_run_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("run.zed", BARE);
    assert_eq!(rejection("run", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_replay_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("replay.zed", BARE);
    assert_eq!(rejection("replay", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_build_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("build.zed", BARE);
    assert_eq!(rejection("build", &f), format!("{}\n", bare_rejection(&f)));
}

#[test]
fn zedc_test_prints_a_parse_error_with_its_steps_and_repairs() {
    let f = file("test.zed", BARE);
    assert_eq!(
        rejection("test", &f),
        format!(
            "{}\n0 passed, 1 failed, 0 rejection units\n",
            bare_rejection(&f)
        )
    );
}

/// Units rejected by their syntax, most with a derivation: each phase of the syntax (a
/// character no token starts with, a parse error, and an item that cannot be built), errors of
/// the syntax with steps, and a unit with two errors, both printed.
const SYNTAX: [(&str, &str); 12] = [
    ("bare", BARE),
    (
        "bare_indexed",
        "f(n) = {\n  d[i in 3..<n] = d[i - 1] + 1 with d = 0;\n  d[n - 1]\n};\n",
    ),
    ("character", "x = 1 # 2;\n"),
    ("parse", "f(x) = x +;\n"),
    ("named_first", "g(a, b: int) = a;\ny = g(b: 1, 2);\n"),
    ("argument_twice", "g(a: int) = a;\ny = g(a: 1, a: 2);\n"),
    ("minus_chain", "y = -3.max(1);\n"),
    ("set_and_map", "y = {1, 2 -> 3};\n"),
    ("two_exports", "f(x) = {\n  return x;\n  return 1;\n};\n"),
    (
        "two_initials",
        "f(n) = loop t {\n  while t < n;\n  initial x = 0;\n  x' = x + 1;\n  \
         initial x = 1;\n};\n",
    ),
    ("field_twice", "s = {a: 1};\nt = s with { a = 2, a = 3 };\n"),
    ("two_errors", "y = {1, 2 -> 3};\nz = {1 -> 2, 3};\n"),
];

#[test]
fn every_command_prints_a_syntax_error_as_zedc_run_does() {
    for (name, text) in SYNTAX {
        let f = file(&format!("syntax_{name}.zed"), text);
        let run = rejection("run", &f);
        assert!(
            run.starts_with(&format!("{}:", f.display())),
            "{name}: {run}"
        );
        // Each has its steps but the lexical error (the plain parse error has one, what was
        // expected at its place), and the last unit has two errors, each after the file's name.
        if name == "two_initials" {
            assert!(
                run.contains(
                    ":5:3: `x` is given its sentinel value, its value before step 0, twice in \
                     this loop: first by `initial x = 0;`, then by `initial x = 1;`."
                ),
                "{name}: {run}"
            );
        }
        let steps = run.contains("\n  [1] ");
        assert_eq!(steps, name != "character", "{name}: {run}");
        let errors = run.matches(&format!("{}:", f.display())).count();
        assert_eq!(
            errors,
            if name == "two_errors" { 2 } else { 1 },
            "{name}: {run}"
        );
        for command in ["fmt", "replay", "build"] {
            assert_eq!(rejection(command, &f), run, "zedc {command} on {name}");
        }
        // `zedc test` counts each error of the unit as one failed check.
        assert_eq!(
            rejection("test", &f),
            format!("{run}0 passed, {errors} failed, 0 rejection units\n"),
            "zedc test on {name}"
        );
    }
}

/// A unit whose syntax is accepted and whose call is rejected by the checker, with a step and
/// two repairs.
const CHECKED: &str =
    "g(a: int, b: int) = a + b;\nmain(m: MainArgs) {\n  m.stdout <- \"${g(1)}\";\n}\n";

#[test]
fn a_rejection_by_the_checker_prints_alike_and_zedc_fmt_lays_the_unit_out() {
    let f = file("checked.zed", CHECKED);
    let run = rejection("run", &f);
    assert_eq!(
        run,
        format!(
            "{}:3:20: this argument is passed by position, and the parameter it reaches, `a` of \
             `g`, is a named parameter, which a call passes only by name, as `a: …`.\n  \
             [1] 1:1: `g` is declared here with no type written for its result; the type the \
             checker found for `g` is `(a: int, b: int) -> int`\n      \
             1 | g(a: int, b: int) = a + b;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
             [2] 3:20: repair: pass `a` by name, as `a: …`\n      \
             3 |   m.stdout <- \"${{g(1)}}\";\n        \
             |                    ^\n  \
             [3] 3:20: repair: declare `a` `positional` in `g`\n",
            f.display()
        )
    );
    for command in ["replay", "build"] {
        assert_eq!(rejection(command, &f), run, "zedc {command}");
    }
    assert_eq!(
        rejection("test", &f),
        format!("{run}0 passed, 1 failed, 0 rejection units\n")
    );
    let (status, out, err) = zedc("fmt", &f, &[]);
    assert_eq!((status, out.as_str(), err.as_str()), (Some(0), CHECKED, ""));
}

/// A manifest is read with the syntax of a unit, and its parse error prints its steps too.
#[test]
fn a_parse_error_in_a_manifest_prints_its_steps_and_repairs() {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("l01_29_commands_binary_package");
    std::fs::create_dir_all(&d).unwrap();
    let manifest = d.join("zed.manifest");
    std::fs::write(&manifest, "prelude = \"std.prelude\" with y = 0;\n").unwrap();
    let f = d.join("a.zed");
    std::fs::write(&f, "main(m: MainArgs) {\n  m.stdout <- \"hi\";\n}\n").unwrap();
    assert_eq!(
        rejection("run", &f),
        format!(
            "{}:1:30: `with y = 0` stands on `prelude = \"std.prelude\" with y = 0;`, which is \
             neither an indexed definition nor a statement of the body of a `loop`, and it gives \
             `y` no sentinel value: without `initial` or a key, it reads as though `y` took the \
             value `0` anew on every step. A `with` clause stands only on an indexed definition, \
             as `y[i in 0..<n] = … with y[-1] = 0;`, and a variable a loop updates takes its \
             sentinel value from a statement of the loop's body, `initial y = 0;`.\n  \
             [1] 1:1: the statement the `with` clause stands on\n      \
             1 | prelude = \"std.prelude\" with y = 0;\n        \
             | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [1]\n        \
             |                              ^^^^^ [2]\n  \
             [2] 1:30: repair: `prelude = \"std.prelude\";`, the `with` clause deleted\n",
            manifest.display()
        )
    );
}

/// A tuple of one value that holds an atom with a payload of one value, `(#ok(1), 2)`: the
/// message names the type as that value, with no article, as it names `true` or `"km"`
/// (MSG-article-atom-value).
const ONE_ATOM: &str = "main(m: MainArgs) {\n  t = (#ok(1), 2);\n  m.stdout <- \"${t == 1}\";\n}\n";

#[test]
fn a_type_of_one_value_that_holds_an_atom_is_written_with_no_article() {
    let f = file("one_atom.zed", ONE_ATOM);
    let run = rejection("run", &f);
    assert_eq!(
        run,
        format!(
            "{}:3:23: No number equals `(#ok(1), 2)`: `t : (#ok(1), 2) == 1` always gives the \
             same answer. Try `m.stdout <- \"${{t[1] == 1}}\"` instead.\n  \
             [1] 3:18: `t` is (#ok(1), 2) here\n      \
             3 |   m.stdout <- \"${{t == 1}}\";\n        \
             |                  ^\n  \
             [2] 2:7: `t` is defined as this expression, (#ok(1), 2)\n      \
             2 |   t = (#ok(1), 2);\n        \
             |       ^^^^^^^^^^^ [2, 3]\n        \
             |        ^^^^^^ [4]\n        \
             |            ^ [5]\n        \
             |                ^ [6]\n  \
             [3] 2:7: this expression gives (#ok(1), 2)\n  \
             [4] 2:8: this atom `#ok` with its payload gives #ok(1)\n  \
             [5] 2:12: this literal, 1, is 1\n  \
             [6] 2:16: this literal, 2, is 2\n  \
             fixes, each checked here:\n    \
             m.stdout <- \"${{t[1] == 1}}\";    compares component 1\n",
            f.display()
        )
    );
    assert_eq!(
        rejection("test", &f),
        format!("{run}0 passed, 1 failed, 0 rejection units\n")
    );
}

/// The contrast: the payload holds every `int`, so `(#ok(int), 2)` has many values and keeps
/// its article.
const MANY_ATOMS: &str = "same(positional n: int) = (#ok(n), 2) == 1;\n\nmain(m: MainArgs) {\n  \
                          m.stdout <- \"${same(3)}\";\n}\n";

#[test]
fn a_type_that_holds_an_atom_of_many_payloads_keeps_its_article() {
    let f = file("many_atoms.zed", MANY_ATOMS);
    assert_eq!(
        rejection("run", &f),
        format!(
            "{}:1:42: No number equals a `(#ok(int), 2)`: `1` compared by `==` with a \
             `(#ok(int), 2)` always gives the same answer. Try `same(positional n: int) = \
             (#ok(n), 2)[1] == 1` instead.\n  \
             [1] 1:27: this expression gives (#ok(int), 2)\n      \
             1 | same(positional n: int) = (#ok(n), 2) == 1;\n        \
             |      ^^^^^^^^^^^^^^^^^ [4] ^^^^^^ [2]\n        \
             |                           ^^^^^^^^^^^ [1]\n        \
             |                                ^ [3]\n        \
             |                                    ^ [5]\n  \
             [2] 1:28: this atom `#ok` with its payload gives #ok(int)\n  \
             [3] 1:32: `n` is int here\n  \
             [4] 1:6: `n` is declared `int`\n  \
             [5] 1:36: this literal, 2, is 2\n  \
             fixes, each checked here:\n    \
             same(positional n: int) = (#ok(n), 2)[1] == 1;    compares component 1\n",
            f.display()
        )
    );
}

/// MAKER-file-chain (COMPLEXITY.md K109): `u = a2 + 1;` after a chain of names each holding the
/// one before, and `u = t2 + 1;` after a tuple doubled twice. Looking for a repair lists the
/// values of the left side (`Type::each_value`), which files each type of the chain once; the
/// message, which offers no repair, is the one `zedc run` printed before that change.
const CHAIN: &str = "a0 = (0, 0);\na1 = (a0, 1);\na2 = (a1, 2);\nu = a2 + 1;\n";
const DOUBLED: &str = "t0 = (1, 1);\nt1 = (t0, t0);\nt2 = (t1, t1);\nu = t2 + 1;\n";

#[test]
fn zedc_run_prints_the_rejection_of_1_added_to_a_chain_of_names() {
    let f = file("chain.zed", CHAIN);
    assert_eq!(
        rejection("run", &f),
        format!(
            "{}:{}",
            f.display(),
            r#"4:5: `+` does not take ((T1, 2), 1): no arrow of `+` takes these types.
  T1 stands for a part written more than once:
    type T1 = ((0, 0), 1);
  [1]  4:5: `a2` is (T1, 2) here
       4 | u = a2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [15, 16, 17]
         |          ^ [14]
  [2]  3:6: `a2` is defined as this expression, (T1, 2)
       3 | a2 = (a1, 2);
         |      ^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^ [13]
  [3]  3:6: this expression gives (T1, 2)
  [4]  3:7: `a1` is T1 here
  [5]  2:6: `a1` is defined as this expression, T1
       2 | a1 = (a0, 1);
         |      ^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^ [12]
  [6]  2:6: this expression gives T1
  [7]  2:7: `a0` is (0, 0) here
  [8]  1:6: `a0` is defined as this expression, (0, 0)
       1 | a0 = (0, 0);
         |      ^^^^^^ [8, 9]
         |       ^ [10]
         |          ^ [11]
  [9]  1:6: this expression gives (0, 0)
  [10] 1:7: this literal, 0, is 0
  [11] 1:10: this literal, 0, is 0
  [12] 2:11: this literal, 1, is 1
  [13] 3:11: this literal, 2, is 2
  [14] 4:10: this literal, 1, is 1
  [15] 4:5: `+` takes (int, int) -> int
  [16] 4:5: `+` takes (f64, f64) -> f64
  [17] 4:5: `+` takes (rat, rat) -> rat
"#
        )
    );
}

#[test]
fn zedc_run_prints_the_rejection_of_1_added_to_a_doubled_tuple() {
    let f = file("doubled.zed", DOUBLED);
    assert_eq!(
        rejection("run", &f),
        format!(
            "{}:{}",
            f.display(),
            r#"4:5: `+` does not take ((T1, T1), 1): no arrow of `+` takes these types.
  T1 stands for a part written more than once:
    type T1 = ((1, 1), (1, 1));
  [1]  4:5: `t2` is (T1, T1) here
       4 | u = t2 + 1;
         |     ^^ [1]
         |     ^^^^^^ [15, 16, 17]
         |          ^ [14]
  [2]  3:6: `t2` is defined as this expression, (T1, T1)
       3 | t2 = (t1, t1);
         |      ^^^^^^^^ [2, 3]
         |       ^^ [4]
         |           ^^ [13]
  [3]  3:6: this expression gives (T1, T1)
  [4]  3:7: `t1` is T1 here
  [5]  2:6: `t1` is defined as this expression, T1
       2 | t1 = (t0, t0);
         |      ^^^^^^^^ [5, 6]
         |       ^^ [7]
         |           ^^ [12]
  [6]  2:6: this expression gives T1
  [7]  2:7: `t0` is (1, 1) here
  [8]  1:6: `t0` is defined as this expression, (1, 1)
       1 | t0 = (1, 1);
         |      ^^^^^^ [8, 9]
         |       ^ [10]
         |          ^ [11]
  [9]  1:6: this expression gives (1, 1)
  [10] 1:7: this literal, 1, is 1
  [11] 1:10: this literal, 1, is 1
  [12] 2:11: `t0` is (1, 1) here
  [13] 3:11: `t1` is T1 here
  [14] 4:10: this literal, 1, is 1
  [15] 4:5: `+` takes (int, int) -> int
  [16] 4:5: `+` takes (f64, f64) -> f64
  [17] 4:5: `+` takes (rat, rat) -> rat
"#
        )
    );
}

/// Two broken declarations and a sound one with a type error (step L1.29d): the first leaves a
/// `(` open up to the next line that begins at the first column, the second has an operator
/// with no operand, and the third is checked.
const RECOVERED: &str = "perimeter(positional w, positional h) = 2 * (w + h\n\
                         area(positional w, positional h) = w * * h;\n\
                         show(positional x) = x ++ 1;\n";

/// The two syntax errors of [`RECOVERED`] in `file`, as every command prints them.
fn recovered_syntax(file: &Path) -> String {
    let at = file.display();
    format!(
        "{at}:2:1: Syntax error at `area`. Try \
         `perimeter(positional w, positional h) = 2 * (w + h);` instead.\n  \
         [1] 2:1: expected '(' or '[' or '.' or '?.' or '*.' or '::' or '^' or '*' or '/' or \
         'div' or 'mod' or '+' or '-' or '++' or '..<' or '..=' or '..' or '><' or 'as' or \
         'into' or 'with' or 'without' or '<=' or '<' or '>=' or '>' or 'is' or 'not' or 'in' \
         or '==' or '!=' or '&&' or '||' or 'else' or ')' or ','\n      \
         2 | area(positional w, positional h) = w * * h;\n        \
         | ^^^^\n  \
         [2] 1:1: the declaration of `perimeter` begins here\n      \
         1 | perimeter(positional w, positional h) = 2 * (w + h\n        \
         | ^^^^^^^^^ [2]                               ^ [3] ^ [5]\n  \
         [3] 1:45: `(` opens here and is still open at `area`\n  \
         [4] 2:1: this line begins at the first column, so it begins the next declaration\n  \
         [5] 1:51: repair: `perimeter(positional w, positional h) = 2 * (w + h);`\n\
         {at}:2:40: Syntax error at `*`. Try `area(positional w, positional h) = w * h;` \
         instead.\n  \
         [1] 2:40 to 2:40: expected '-' or '!' or an annotation such as `@name` or a number or \
         a string or 'true' or 'false' or an atom such as `#name` or a name or 'this' or '(' or \
         'if' or 'match' or 'for' or 'loop' or '[' or '{{' or '?'\n      \
         line 2 is shown above\n  \
         [2] 2:1 to 2:4: the declaration of `area` begins here\n  \
         [3] 2:40 to 2:41: repair: `area(positional w, positional h) = w * h;`\n"
    )
}

#[test]
fn zedc_run_prints_each_syntax_error_and_the_type_errors_of_the_declarations_that_parse() {
    let f = file("recovered.zed", RECOVERED);
    let run = rejection("run", &f);
    assert_eq!(
        run,
        format!(
            "{}{}:3:22: `++` does not take (String, 1): no arrow of `++` takes these types.\n  \
             [1] 3:22: `x` is String here\n      \
             3 | show(positional x) = x ++ 1;\n        \
             |      ^^^^^^^^^^^^ [2]     ^ [3]\n        \
             |                      ^ [1]\n        \
             |                      ^^^^^^ [4, 5]\n  \
             [2] 3:6: `x` has no declared type; its uses give it String\n  \
             [3] 3:27: this literal, 1, is 1\n  \
             [4] 3:22: `++` takes (String, String) -> String\n  \
             [5] 3:22: `++` takes String\n",
            recovered_syntax(&f),
            f.display()
        )
    );
    for command in ["replay", "build"] {
        assert_eq!(rejection(command, &f), run, "zedc {command}");
    }
    // `zedc fmt` reads the syntax only: it prints the syntax errors and no type error.
    assert_eq!(rejection("fmt", &f), recovered_syntax(&f));
    // Each repair offered, written in place of its line, parses.
    let fixed = RECOVERED
        .replace("2 * (w + h\n", "2 * (w + h);\n")
        .replace("w * * h", "w * h");
    let f = file("recovered_fixed.zed", &fixed);
    let run = rejection("run", &f);
    assert!(!run.contains("Syntax error"), "{run}");
}

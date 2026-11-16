//! Plan row MAP-stdin-ioerror: an `#ioError` in a value pushed to a `Lines` port bubbles out of
//! `main` (sec:failure, atoms bubble out of an argument; sec:ports: a failure
//! that bubbles out of `main` exits with 1). EXAMPLES.md "[1. Programs and ports] 2",
//! `m.stdout <- m.stdin.map(l -> l.upper);`, is taken by the checker: on input that is all
//! UTF-8 it writes the lines upper-cased, and on a line that is not UTF-8, which `m.stdin`
//! reads as `#ioError`, the run writes nothing and exits with 1. `zedc run` and the
//! executable `zedc build` makes agree on both. A push elsewhere than as a statement of the
//! body of `main` is refused by name (plan row PUSH-bubble-nested).

use zed_tests::step_helpers::l01_36a_executables::{Ran, built, dir, executable, interpreter};

/// `text` saved as `name.zed`, run by `zedc run` and by the executable `zedc build` makes, each
/// with `stdin` as its input; both runs must agree, and the one result is returned.
fn both(name: &str, text: &str, stdin: &[u8]) -> Ran {
    let d = dir(&format!("l03_02_map_run/{name}"));
    let src = d.join(format!("{name}.zed"));
    std::fs::write(&src, text).unwrap();
    let ran = interpreter(&src, &[], stdin);
    let exe = d.join(name);
    built(&src, &exe);
    assert_eq!(
        executable(&exe, &[], stdin),
        ran,
        "{name}: native and interpreted runs"
    );
    ran
}

const UPPER: &str = "main(m: MainArgs) {\n    m.stdout <- m.stdin.map(l -> l.upper);\n}\n";

#[test]
fn a_push_of_stdin_mapped_writes_the_lines_upper_cased() {
    let ran = both("upper_ok", UPPER, b"ab\ncd\n");
    assert_eq!(
        (ran.status, ran.stdout.as_str()),
        (0, "AB\nCD\n"),
        "{ran:?}"
    );
}

#[test]
fn a_line_that_is_not_utf8_ends_the_run_with_status_1_and_writes_nothing() {
    let ran = both("upper_bad", UPPER, b"ab\n\xff\ncd\n");
    assert_eq!((ran.status, ran.stdout.as_str()), (1, ""), "{ran:?}");
    assert!(ran.stderr.contains("#ioError"), "{ran:?}");
    assert!(
        ran.stderr.contains(
            "to `m.stdout`, a failure, which ends the run of `main`: nothing is \
             written, and the exit status is 1"
        ),
        "{ran:?}"
    );
}

#[test]
fn a_read_of_a_range_is_handled_before_the_push() {
    // A missed read's atom is the program's own, which it can handle where it makes it: only
    // `#ioError` bubbles out of a push, and the miss is handled with `else`. The key is one the
    // checker cannot know, as the run passes no argument: a read at a literal key outside the
    // range is a static error (row RANGE-literal-reads).
    let text = |k: u8| {
        format!(
            "main(m: MainArgs) {{\n    m.stdout <- \
             \"${{(0 ..< 3)[if m.args.count > 0 {{ 0 }} else {{ {k} }}] else -1}}\";\n}}\n"
        )
    };
    let ran = both("range_hit", &text(1), b"");
    assert_eq!((ran.status, ran.stdout.as_str()), (0, "1\n"), "{ran:?}");
    let ran = both("range_miss", &text(3), b"");
    assert_eq!((ran.status, ran.stdout.as_str()), (0, "-1\n"), "{ran:?}");
}

#[test]
fn a_push_of_an_atom_the_program_makes_is_still_refused() {
    let d = dir("l03_02_map_run/range_unhandled");
    let src = d.join("range_unhandled.zed");
    std::fs::write(
        &src,
        // A key the checker cannot know: `(0 ..< 3)[1]` has no miss (row RANGE-literal-reads).
        "main(m: MainArgs) {\n    m.stdout <- \"${(0 ..< 3)[m.args.count]}\";\n}\n",
    )
    .unwrap();
    let ran = interpreter(&src, &[], b"");
    assert_ne!(ran.status, 0, "{ran:?}");
    assert!(
        ran.stderr
            .contains("A `Lines` port takes a `String` or a family of strings"),
        "{ran:?}"
    );
    assert!(ran.stderr.contains("#outOfBounds"), "{ran:?}");
}

#[test]
fn a_push_elsewhere_than_in_the_body_of_main_is_not_built() {
    // The lines of `inp` may be `#ioError`, in a function that takes the port: its failure
    // would be the value of `say`.
    let text = "say(inp: Lines, out: Lines) {\n    out <- inp.map(l -> l.upper);\n}\n\
                main(m: MainArgs) {\n    _ = say(inp: m.stdin, out: m.stdout);\n}\n";
    let d = dir("l03_02_map_run/push_nested");
    let src = d.join("push_nested.zed");
    std::fs::write(&src, text).unwrap();
    let ran = interpreter(&src, &[], b"ab\n");
    assert_ne!(ran.status, 0, "{ran:?}");
    assert!(
        ran.stderr
            .contains("a push of a value that may be the atom `#ioError`"),
        "{ran:?}"
    );
    assert!(ran.stderr.contains("does not compile it yet"), "{ran:?}");
}

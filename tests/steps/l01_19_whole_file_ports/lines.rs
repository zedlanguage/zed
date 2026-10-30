//! `Lines` ports: standard input as the family of its lines, keyed from 1, and a pushed
//! string or family written as lines.

use zed_kernel::Value;
use zedc::run::split_lines;

use super::run;

#[test]
fn cat_echoes_standard_input_line_by_line() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin;\n}\n";
    let out = run("cat", src, "first\nsecond\n", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, "first\nsecond\n"));
    // A last line without `\n` is still a line, and is written with one.
    let out = run("cat", src, "only", &[]);
    assert_eq!(out.stdout, "only\n");
    // An empty input has no lines, so nothing is written.
    let out = run("cat", src, "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (0, ""));
}

#[test]
fn lines_are_numbered_from_one_and_crlf_is_one_line_end() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- \"${stdin[1]}|${stdin[2]}|${stdin[3] else \"none\"}\";\n}\n";
    let out = run("numbers", src, "name: Ada\r\nrole: admin\r\n", &[]);
    assert_eq!(out.stdout, "name: Ada|role: admin|none\n");
    assert_eq!(
        split_lines(b"a\r\n\nb").to_string(),
        "{1 -> \"a\", 2 -> \"\", 3 -> \"b\"}",
        "an empty line in the middle is kept"
    );
}

#[test]
fn a_line_that_is_not_utf8_is_an_io_error_at_its_key() {
    let lines = split_lines(b"ok\n\xff\xfe\nfine\n");
    let Value::Family(f) = &lines else {
        panic!("{lines}")
    };
    assert_eq!(f.get(&Value::Int(1)), Some(&Value::str("ok")));
    assert_eq!(f.get(&Value::Int(2)), Some(&Value::atom("ioError")));
    assert_eq!(f.get(&Value::Int(3)), Some(&Value::str("fine")));
}

#[test]
fn a_greeting_reads_one_line_and_writes_one() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  \
               name = trim(stdin[1]) else \"stranger\";\n  \
               stdout <- \"Hello, ${name}!\";\n}\n";
    assert_eq!(
        run("greet", src, "  Grace \n", &[]).stdout,
        "Hello, Grace!\n"
    );
    assert_eq!(run("greet", src, "", &[]).stdout, "Hello, stranger!\n");
}

#[test]
fn a_computed_line_number_reads_that_line() {
    // The first line says which later line to print; a key that is not a literal reads the
    // family by value, as a literal one does.
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  \
               pick = int(stdin[1]) else 0;\n  \
               stdout <- stdin[pick + 1] else \"no such line\";\n}\n";
    assert_eq!(
        run("pick", src, "2\nred\ngreen\nblue\n", &[]).stdout,
        "green\n"
    );
    assert_eq!(run("pick", src, "9\nred\n", &[]).stdout, "no such line\n");
}

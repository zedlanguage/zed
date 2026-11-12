//! A question the checker refuses in a unit it accepts reaches `zedc` output as a placed
//! warning with its derivation (DESIGN.md L1.39; WARN-refused): on standard error, at the test
//! or read that asked it, in order of place and then of question, from `zedc run` and `zedc test`
//! alike, the same in a batch as alone, and only for a unit with no rejection.

use zed_tests::scaling;

/// Writes the unit `src` as `file` in test directory `name`, kept apart from the other tests'.
fn unit(name: &str, file: &str, src: &str) -> String {
    super::widen_test::unit(&format!("refused_{name}"), file, src)
}

/// Four conditions on four variables that the checker cannot solve exactly: removing any one
/// variable would leave more conditions than there are (L1.39 "refused questions").
const GROWTH: &str = "4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && \
                      4 * w + 10 * x - 10 * y - 11 * z - 28 >= 0 && \
                      11 * w + 4 * x - y + 12 * z - 28 >= 0 && \
                      0 - 8 * w - 5 * x + 12 * y - z + 31 >= 0";

/// The last conjunct of [`GROWTH`]: the narrowing by it is the one that asks the question.
const LAST: &str = "0 - 8 * w - 5 * x + 12 * y - z + 31 >= 0";

/// [`GROWTH`] with every constant 0: the checker asks for the values of each variable apart,
/// and refuses each.
const GROWTH0: &str = "4 * x - 12 * w - 10 * y - 12 * z >= 0 && \
                       4 * w + 10 * x - 10 * y - 11 * z >= 0 && \
                       11 * w + 4 * x - y + 12 * z >= 0 && \
                       0 - 8 * w - 5 * x + 12 * y - z >= 0";

/// A function `name` that divides by `x` when `test` holds.
fn guarded(name: &str, test: &str) -> String {
    format!("{name}(x: int, y: int, z: int, w: int) = if {test} {{ 100 div x }} else {{ 0 }};\n")
}

/// The unit of the functions `defs`, then a table that passes and an empty `main`.
fn program(defs: &str) -> String {
    format!("{defs}half(positional x) = x div 2 test {{ 10 -> 5, 7 -> 3 }}\nmain() {{\n}}\n")
}

/// `zedc test --addresses <files>`: its status, standard output and standard error.
fn test(files: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = std::iter::once(&"--addresses")
        .chain(files)
        .map(|a| a.to_string())
        .collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::testing::command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

/// `zedc run <file> <more>` with no input: its status and standard error.
fn run(file: &str, more: &[&str]) -> (u8, String) {
    let args: Vec<&str> = ["run", file].iter().chain(more).copied().collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = zedc::run::command(&args, &mut "".as_bytes(), &mut out, &mut err);
    (status, String::from_utf8(err).unwrap())
}

/// The first line of each warning in the standard error `err`.
fn firsts(err: &str) -> Vec<&str> {
    err.lines().filter(|l| !l.starts_with(' ')).collect()
}

#[test]
fn a_refused_test_prints_one_placed_warning() {
    let src = program(&guarded("f", GROWTH));
    let file = unit("refused", "one.zed", &src);
    let line = src.lines().next().unwrap();
    let col = line.find(LAST).unwrap() + 1;
    let address = zedc::suppress::InFile::of(file.as_ref())
        .unwrap()
        .address(&zedc::run::load(src.as_bytes()).unwrap().warnings()[0]);
    let conditions = "12 * w + 10 * y + 12 * z <= 4 * x + 11 && \
                      8 * w + 5 * x + z <= 12 * y + 31 && \
                      4 * w + 10 * x >= 10 * y + 11 * z + 28 && \
                      11 * w + 4 * x + 12 * z >= y + 28";
    let carets = format!("{}{}", " ".repeat(col - 1), "^".repeat(LAST.len()));
    let expected = format!(
        "\
{file}:1:{col}: Cannot find exactly which values meet the conditions here.
  [1] 1:{col}: here the conditions `{conditions}` hold
      1 | {line}
        | {carets}
  [2] 1:{col}: the checker could not work out which values each of their variables can take: \
to find whole numbers that meet these conditions, the checker removes one variable at a time, \
putting in place of the conditions on it conditions on the variables left. Here four variables \
or more are left, and removing any one of them would leave more conditions than there are now, \
so the work could grow without end. The checker stopped there, and the bounds that each \
condition gives each variable from the bounds of the others rule out no value: `w`, `x`, `y` \
and `z` may still be any whole number
  [3] 1:{col}: so here each of their variables keeps only those bounds, which may be wider than \
the conditions allow; so the checker may reject or warn about code here that is correct, and it \
does not accept code that is wrong
  [4] 1:{col}: repair: if `w` is meant to take only one value in the conditions, state that \
value, and the checker removes `w` from the question: `w == 0 && {conditions}`, with the value \
in place of `0`
  address: {address}
"
    );
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "2 passed, 0 failed, 0 rejection units\n");
    assert_eq!(err, expected);
    assert_eq!(run(&file, &["--addresses"]), (0, err));
    // The warning is suppressed by its address, as every warning is.
    assert_eq!(
        run(&file, &["--suppress", &address.to_string()]),
        (0, String::new())
    );
}

#[test]
fn a_test_asked_only_whether_its_arm_is_reached_prints_its_warning() {
    // No read in either arm needs the scope of the test; the arms differ in type, so the
    // checker asks whether any value reaches `#big`, and that question is refused.
    let src = program(&format!(
        "f(x: int, y: int, z: int, w: int) = if {GROWTH} {{ #big }} else {{ 0 }};\n"
    ));
    let file = unit("reached", "reached.zed", &src);
    let col = src.find(LAST).unwrap() + 1;
    let (status, _, err) = test(&[&file]);
    assert_eq!(status, 0);
    assert_eq!(
        firsts(&err),
        [format!(
            "{file}:1:{col}: Cannot find exactly which values meet the conditions here."
        )]
    );
    assert_eq!(run(&file, &["--addresses"]), (0, err));
}

#[test]
fn a_unit_with_no_refusal_prints_no_warning() {
    // `x >= 1` is a question the checker answers; the repair the warning offers is another.
    let repaired = format!("w == 0 && {GROWTH}");
    for (name, test_) in [("plain", "x >= 1"), ("repaired", repaired.as_str())] {
        let file = unit(
            "none",
            &format!("{name}.zed"),
            &program(&guarded("f", test_)),
        );
        assert_eq!(
            test(&[&file]),
            (
                0,
                "2 passed, 0 failed, 0 rejection units\n".into(),
                String::new()
            ),
            "{name}"
        );
        assert_eq!(run(&file, &[]), (0, String::new()), "{name}");
    }
}

#[test]
fn questions_at_one_place_keep_their_order() {
    // Four questions refused at one conjunct: by the variable each asks for, as `Refused` is
    // ordered, not in the order the solver met them.
    let src = program(&guarded("g", GROWTH0));
    let file = unit("order", "one_place.zed", &src);
    let col = src.find("0 - 8 * w").unwrap() + 1;
    let (status, _, err) = test(&[&file]);
    assert_eq!(status, 0);
    let heads: Vec<String> = ["w", "x", "y", "z"]
        .iter()
        .map(|v| format!("{file}:1:{col}: Cannot find exactly which values `{v}` can take here."))
        .collect();
    assert_eq!(firsts(&err), heads);
    assert_eq!(run(&file, &["--addresses"]), (0, err));
}

#[test]
fn warnings_at_several_places_keep_their_order() {
    // The same question asked by two functions is two warnings, one at each; the second
    // function's come after the first's although its questions sort first.
    let src = program(&format!(
        "{}{}",
        guarded("f", GROWTH),
        guarded("g", GROWTH0)
    ));
    let file = unit("order", "two_places.zed", &src);
    let (status, _, err) = test(&[&file]);
    assert_eq!(status, 0);
    let places: Vec<&str> = firsts(&err)
        .iter()
        .map(|l| l[file.len() + 1..].split(": ").next().unwrap())
        .collect();
    assert_eq!(places, ["1:173", "2:158", "2:158", "2:158", "2:158"]);
    let twice = program(&format!("{}{}", guarded("f", GROWTH), guarded("h", GROWTH)));
    let file = unit("order", "twice.zed", &twice);
    let (_, _, err) = test(&[&file]);
    let places: Vec<&str> = firsts(&err)
        .iter()
        .map(|l| l[file.len() + 1..].split(": ").next().unwrap())
        .collect();
    assert_eq!(places, ["1:173", "2:173"]);
}

#[test]
fn a_batch_prints_what_each_file_prints_alone() {
    let a = unit("batch", "a.zed", &program(&guarded("f", GROWTH)));
    let b = unit("batch", "b.zed", &program(&guarded("f", "x >= 1")));
    let c = unit("batch", "c.zed", &program(&guarded("g", GROWTH0)));
    // A second unit asking `a`'s question, checked after it on the same thread.
    let d = unit("batch", "d.zed", &program(&guarded("k", GROWTH)));
    let files = [&a, &b, &c, &d];
    let alone: String = files.iter().map(|f| test(&[f]).2).collect();
    assert_eq!(firsts(&alone).len(), 6);
    assert_eq!(test(&files.map(String::as_str)).2, alone);
    let reversed: String = files.iter().rev().map(|f| test(&[f]).2).collect();
    let mut back = files;
    back.reverse();
    assert_eq!(test(&back.map(String::as_str)).2, reversed);
}

#[test]
fn a_rejected_unit_prints_no_warning() {
    // The refusal is not reported when the unit does not compile; its rejection is.
    let src = program(&format!(
        "{}same(positional x) = x test {{ 1 -> y }}\n",
        guarded("f", GROWTH)
    ));
    let file = unit("rejected", "rejected.zed", &src);
    let (status, out, err) = test(&[&file]);
    assert_eq!(status, 1);
    assert!(out.contains("`y`"), "{out}");
    assert_eq!(err, "");
}

/// A unit of `n` functions, each with a test whose question the checker refuses.
fn many_refusals(n: usize) -> String {
    program(
        &(0..n)
            .map(|i| guarded(&format!("guard{i}"), GROWTH))
            .collect::<String>(),
    )
}

/// `zedc test` on a unit of `n` refused questions, one in each function: checking, placing
/// and printing together are within n log n. The files are written before the timing.
#[test]
fn many_refusals_scale() {
    let n = 40;
    let files = scaling::inputs(n, |m| unit("scale", &format!("{m}.zed"), &many_refusals(m)));
    scaling::check("zedc test on a unit of n refused questions", n, |m| {
        let (status, _, err) = test(&[&files[&m]]);
        assert_eq!(status, 0);
        assert_eq!(firsts(&err).len(), m);
    });
}

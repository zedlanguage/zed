//! The type the checker prints for a parameter of no written type is the set of values calls
//! accept (row TEST-sig-text-printed-type-matches-calls). `Ck::sig_text` prints a parameter
//! whose every need is an argument at a parameter of a closed type (`NeedKind::Into`) as the
//! meet of those types and of its carrier bound; the claim that this meet is exactly what calls
//! accept was checked by hand on five programs only (MSG-bounded-param-printed-underscore). Here
//! each printed type is read from the "type the checker found" note and compared, argument by
//! argument, with what the function accepts: by hand on three programs, then on random ones.
//!
//! A loose atom passed where a closed type does not hold it passes out of the call (DESIGN.md
//! sec:failure, "atoms bubble out of an argument"), at the function as at a function whose
//! parameter is written with the printed type, so the comparison holds for atoms too; the
//! probe that makes the checker print the type is a tuple, which no closed type here holds
//! and which does not pass out.

use super::type_errors;
use zed_tests::instances::Rng;
use zed_tests::seed::seed;

/// The argument the probe call passes: no type of [`CLOSED`] holds it, and it is no atom.
const PROBE: &str = "(1, 2)";

/// The type printed for the function `name` in the report of `src`, which the checker rejects.
fn found(src: &str, name: &str) -> String {
    let report = match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("{src}: accepted"),
        Err(e) => e.to_string(),
    };
    let key = format!("the type the checker found for `{name}` is `");
    let at = report
        .find(&key)
        .unwrap_or_else(|| panic!("{src}: {report}"))
        + key.len();
    report[at..].split('`').next().unwrap().to_string()
}

/// `src` checks with no type error.
fn accepted(src: &str) -> bool {
    type_errors(src).is_empty()
}

/// Definitions, function, printed type, arguments inside, arguments outside.
type Case<'a> = (&'a str, &'a str, &'a str, &'a [&'a str], &'a [&'a str]);

#[test]
fn the_printed_type_of_a_passed_parameter_is_what_calls_accept() {
    let cases: &[Case] = &[
        (
            "takes(n: int | f64 | String) = 1;\nnum(x) = takes(n: x) + x;\n",
            "num",
            "(x: int) -> int",
            &["2", "-7"],
            &["2.5", "\"s\""],
        ),
        (
            "takes(n: int | f64) = 1;\ntwo(x) = takes(n: x) + takes(n: x);\n",
            "two",
            "(x: T) -> int for T in int | f64",
            &["2", "2.5"],
            &["\"s\""],
        ),
        (
            "takes(n: int | f64) = 1;\nalso(n: int | String) = 2;\nboth(x) = takes(n: x) + also(n: x);\n",
            "both",
            "(x: int) -> int",
            &["3"],
            &["2.5", "\"s\""],
        ),
    ];
    for (defs, f, want, inside, outside) in cases {
        let probe = format!("{defs}a = {f}(x: {PROBE});\n");
        assert_eq!(found(&probe, f), *want, "{probe}");
        for v in *inside {
            let src = format!("{defs}a = {f}(x: {v});\n");
            assert!(accepted(&src), "{src}: rejected, though {v} is in {want}");
        }
        for v in *outside {
            let src = format!("{defs}a = {f}(x: {v});\n");
            assert!(
                !accepted(&src),
                "{src}: accepted, though {v} is not in {want}"
            );
        }
    }
}

/// Row FAIL-atom-into-arrow-param-not-passed-out: a loose atom passed for a parameter whose
/// every use is an argument at a function type passes by the call, as at a function whose
/// parameter is written with that type (rule 6 of sec:type_resolution), and the call gives it.
/// Red before: "`t0` does not take #a, only f64 -> f64" at `g`'s call, while `h` accepted.
/// An atom the printed type holds still enters, and a parameter that stands twice, which
/// prints as a type variable, still lets every atom in (the controls in l01_27 loose.rs).
#[test]
fn an_atom_passes_by_a_parameter_passed_into_a_function_type() {
    for ty in ["f64 -> f64", "int ->? int", "(int) -> int"] {
        let defs =
            format!("t0(n: {ty}) = 1;\ng(x, c: bool) = (if c {{ t0(n: x) }} else {{ 0 }});\n");
        let call = format!("{defs}a = g(x: #a, c: true);\n");
        assert_eq!(type_errors(&call), Vec::<String>::new(), "{call}");
        let typed = format!("h(y: {ty}) = 1;\na = h(y: #a);\n");
        assert_eq!(type_errors(&typed), Vec::<String>::new(), "{typed}");
    }
    // Two uses at two function types: the meet holds no atom, so the atom passes by.
    let two = "t0(n: f64 -> f64) = 1;\nt1(n: int -> int) = 2;\ng(x) = t0(n: x) + t1(n: x);\n";
    assert_eq!(
        type_errors(&format!("{two}a = g(x: #a);\n")),
        Vec::<String>::new()
    );
    // A use at a type that holds the atom takes it: it enters and is no error.
    let holds = "t0(n: f64 | String | #a) = 1;\ng(x) = t0(n: x);\n";
    assert_eq!(
        type_errors(&format!("{holds}a = g(x: #a);\n")),
        Vec::<String>::new()
    );
    // A parameter that also stands in the result is a type variable: the atom enters and the
    // use refuses it, as before.
    let twice = "t0(n: f64 -> f64) = 1;\ng(x) = (t0(n: x), x);\n";
    let errors = type_errors(&format!("{twice}a = g(x: #a);\n"));
    assert!(
        errors.iter().any(|e| e.contains("`t0` does not take #a")),
        "{errors:?}"
    );
}

/// The closed types a random use passes `x` into.
const CLOSED: &[&str] = &[
    "int",
    "f64",
    "String",
    "#a | #b",
    "int | f64",
    "int | String",
    "f64 | String | #a",
    "int -> int",
    "int ->? int",
    "f64 -> f64",
];

/// The arguments each random function is called with: at least one inside and one outside
/// each type of [`CLOSED`].
const ARGS: &[&str] = &[
    "2",
    "2.5",
    "\"s\"",
    "#a",
    "#c",
    "(positional y: int) -> y + 1",
    "(positional y: f64) -> y * 2.0",
];

/// The parameter type of `x` in the printed type `printed` of `g(x, c: bool) -> ...`; for a
/// type variable printed with its bound, `(x: T, c: bool) -> int for T in int | f64`, the bound.
fn x_type(printed: &str) -> &str {
    if let Some((_, bound)) = printed.split_once(" for T in ") {
        return bound;
    }
    let rest = printed
        .strip_prefix("(x: ")
        .unwrap_or_else(|| panic!("{printed}"));
    let end = rest
        .find(", c: bool) -> ")
        .unwrap_or_else(|| panic!("{printed}"));
    &rest[..end]
}

/// Random functions `g(x, c: bool)` that pass `x` to one to three parameters of closed types,
/// some under an `if`: each argument of [`ARGS`] is accepted by `g` exactly when it is
/// accepted by a function whose parameter is written with the printed type of `x`. The printed
/// type is syntax (it parses and checks as a written type), and it is the set of values calls
/// accept. A `g` whose uses no value fits is rejected at its own body and prints no type for
/// a call, so it is left out, and functions are drawn until 40 are compared: a fixed 40 draws
/// with at least 10 compared failed at seed 11005775722037183794, which drew only 9 accepted
/// (FREE2-batch-b23). About one draw in five is accepted, so 1000 draws, about 9 s at most,
/// hold 40 at any seed met. Each run takes a new seed and prints it; `ZED_TEST_SEED=<seed>`
/// repeats it.
#[test]
fn random_printed_parameter_types_are_what_calls_accept() {
    let mut rng = Rng::new(seed("random_printed_parameter_types_are_what_calls_accept"));
    let mut compared = 0;
    let mut drawn = 0;
    while compared < 40 && drawn < 1000 {
        drawn += 1;
        let uses = 1 + rng.below(3);
        let mut defs = String::new();
        let mut body = Vec::new();
        for i in 0..uses {
            defs.push_str(&format!("t{i}(n: {}) = 1;\n", rng.pick(CLOSED)));
            let call = format!("t{i}(n: x)");
            body.push(if rng.coin() {
                format!("(if c {{ {call} }} else {{ 0 }})")
            } else {
                call
            });
        }
        let defs = format!("{defs}g(x, c: bool) = {};\n", body.join(" + "));
        if !accepted(&defs) {
            continue;
        }
        let probe = format!("{defs}a = g(x: {PROBE}, c: true);\n");
        let printed = found(&probe, "g");
        let ty = x_type(&printed);
        let typed = format!("{defs}h(y: {ty}) = 1;\n");
        assert!(
            accepted(&typed),
            "{typed}: the printed type {ty} does not check"
        );
        for v in ARGS {
            // A loose atom passed on into a parameter of an arrow type passes by `g`'s call as
            // by `h`'s (row FAIL-atom-into-arrow-param-not-passed-out, which removed the skip
            // of atoms at arrow types here).
            let g_errors = type_errors(&format!("{defs}a = g(x: {v}, c: true);\n"));
            let by_g = g_errors.is_empty();
            let h_errors = type_errors(&format!("{typed}a = h(y: {v});\n"));
            let by_h = h_errors.is_empty();
            assert_eq!(
                by_g, by_h,
                "{defs}printed `{printed}`; argument {v}: g accepts {by_g}, `{ty}` holds \
                 {by_h}\ng: {g_errors:?}\nh: {h_errors:?}"
            );
        }
        compared += 1;
    }
    assert_eq!(compared, 40, "only {compared} functions compared in {drawn} draws");
}

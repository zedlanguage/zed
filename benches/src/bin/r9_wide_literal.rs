//! Hand-run probe of REFUSAL-front-rest (docs/handoff/REFUSAL-front-unsolved.md), moved out of
//! `tests/steps/l01_23_subtyping/refusals.rs`, where it was built only under a cfg switch: prints
//! how the integer literals at and past the 64-bit bounds read, as a type and as the parameter
//! type of a program, and asserts nothing. `r9_wide_literal` takes no arguments.

use zed_kernel::Value;

fn main() {
    for text in [
        "9223372036854775807",
        "9223372036854775808",
        "-9223372036854775809",
        "18446744073709551616",
    ] {
        let v = Value::int(text.parse().unwrap());
        let ty = zedc::check::read::parse_type(text);
        match ty {
            Ok(t) => eprintln!(
                "r9 literal {text}: empty {} contains_literal {} contains_zero {}",
                t.is_empty(),
                t.contains(&v),
                t.contains(&Value::Int(0))
            ),
            Err(e) => eprintln!("r9 literal {text}: error {e}"),
        }
        for arg in [text, "0"] {
            let src = format!("f(x: {text}) = 0;\nmain() = f(x: {arg});\n");
            eprintln!(
                "r9 literal program {text} arg {arg}: {:?}",
                zedc::run::load(src.as_bytes()).err()
            );
        }
    }
}

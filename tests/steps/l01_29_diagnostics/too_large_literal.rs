//! A number literal whose digits the system refuses the memory to copy (plan row
//! MSG-too-large-literal-repair; DESIGN.md sec:diagnostics, a repair written as code): the
//! message names the size and gives, as code, the number read from a file when the program
//! runs, with the cast of the literal's own kind, which moves the size check to the run (the
//! repair "an operand read from the input" of the row "Number too large for any memory of the
//! target"). The refusal itself is a test of l01_17 (memory_check.rs), which lowers a child's
//! memory limit; here each repair is held to compile.

use num_bigint::BigUint;
use zed_kernel::num::TooLarge;
use zedc::build::Build;
use zedc::run::load_for;

/// A refusal of a number of 2^40 bits whose copy asked for 2^43 bits.
fn refusal() -> TooLarge {
    TooLarge {
        size: BigUint::from(1u32) << 40u32,
        ask: BigUint::from(1u32) << 43u32,
    }
}

/// The code of `message` written last between backticks.
fn last_code(message: &str) -> &str {
    let mut parts = message.rsplit('`');
    parts.next();
    parts.next().expect("a repair written as code")
}

#[test]
fn a_literal_too_large_for_memory_is_refused_with_a_repair_written_as_code() {
    let read = r#"main::files["n.txt"] else #ioError -> "0" else #notFound -> "0""#;
    for (cast, zero) in [("int", "0"), ("rat", "0r"), ("f64", "0.0"), ("f32", "0.0f32")] {
        let message = zedc::lex::unread_literal(&refusal(), cast);
        let number = refusal().number();
        let repair = format!("{cast}({read}) else #invalid -> {zero}");
        assert_eq!(
            message,
            format!(
                "Number too large for memory: this literal needs {number}. Write it with \
                 fewer digits, or read it from a file when the program runs: `{repair}`."
            )
        );
        // The repair compiles where the literal stood.
        let src = format!(
            "main(m: MainArgs) {{\n    n = {};\n    m.stdout <- String(n);\n}}\n",
            last_code(&message)
        );
        let build = Build::default().for_target("x86_64-linux");
        assert_eq!(load_for(src.as_bytes(), &build).err(), None, "{src}");
    }
}

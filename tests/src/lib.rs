//! Shared helpers for the step tests in `tests/steps/`.
//!
//! Each step of DESIGN.md Part G has one folder, `tests/steps/<step>/`, holding that step's
//! tests and the Zed fixtures they read; expected outputs are `insta` snapshots in the folder's
//! `snapshots/` directory, accepted with `cargo insta review` (docs/layout.md).

use std::path::PathBuf;

pub mod check;
pub mod deep;
pub mod fences;
pub mod instances;
pub mod kernel;
pub mod layout;
pub mod oracle;
pub mod readme;
pub mod scaling;
pub mod seed;
pub mod step_helpers;
pub mod tokens;
pub mod trees;

/// A Zed function that doubles a string, for [`too_long`].
pub const TWICE: &str = "twice(positional s: String) = s ++ s;\n";

/// A Zed expression that stops evaluation at run time: `"a"` doubled by [`TWICE`] 64 times,
/// whose `2^64` bytes no string's length holds, so the last `++` refuses.
pub fn too_long() -> String {
    format!("{}\"a\"{}", "twice(".repeat(64), ")".repeat(64))
}

/// The message for `what`, a string literal naming a form or prelude name of Zed that this
/// zedc does not compile yet, as a `&'static str`, for a list of expected messages:
/// `not_yet!("a `match`")`. Written out here, so a test checks the text, not a call.
#[macro_export]
macro_rules! not_yet {
    ($what:literal) => {
        concat!(
            $what,
            " is part of the Zed language, and this version of zedc does not compile it yet. \
             Write the program without it, with the forms this zedc compiles."
        )
    };
}

/// [`not_yet!`] for `what` built at run time, as `the prelude word `any``.
pub fn not_yet(what: &str) -> String {
    format!("{what}{}", not_yet!(""))
}

/// The message for the use of `what`, a definition in another unit, as
/// ``"`shapes.area`, a definition of another unit,"``.
pub fn not_linked(what: &str) -> String {
    format!(
        "{what} is used here, and this version of zedc does not yet link a use to a definition \
         in another unit. Write the definition in this file instead, and use it from there."
    )
}

/// The message for an `import` statement, which this zedc does not link yet, as a literal, for
/// `concat!`.
#[macro_export]
macro_rules! import_not_yet {
    () => {
        "an import is part of the Zed language, and this version of zedc does not yet tie a name \
         an import brings in to the other unit's definition. Write the definitions this file \
         uses in it, and remove the import."
    };
}

/// [`import_not_yet!`] as a constant.
pub const IMPORT_NOT_YET: &str = import_not_yet!();

/// The message for the use of `name`, which nothing in scope and nothing in the prelude defines.
pub fn undefined(name: &str) -> String {
    format!("`{name}` is not defined.")
}

/// The message for the type `name`, which no type in scope and no prelude type has as its name.
pub fn undefined_type(name: &str) -> String {
    format!("The type `{name}` is not defined.")
}

/// Whether `message` reports a form or a link this zedc does not compile yet ([`not_yet()`],
/// [`not_linked`] and [`IMPORT_NOT_YET`]).
pub fn is_not_yet(message: &str) -> bool {
    message.contains("this version of zedc does not compile it yet")
        || message.contains("this version of zedc does not yet link")
        || message.contains("this version of zedc does not yet tie")
}

/// The headline for the parameter `name` of `main`, declared as `name: written`, a type that is
/// not `MainArgs`.
pub fn main_param_message(name: &str, written: &str) -> String {
    format!(
        "Parameter of `main` that is not a `MainArgs`: `{name}: {written}`. Try \
         `main(m: MainArgs)` instead."
    )
}

/// The folder that holds every step folder.
pub fn steps_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("steps")
}

/// The last layer DESIGN.md has (`L40`, a browser layout engine in Zed).
const LAST_LAYER: u8 = 40;

/// Whether `name` is a well-formed step-folder name: a stage (`m0`, `l01`…`l40` for the layers
/// L1 to L40 of DESIGN.md, or `s` for the self-hosting row), the two-digit step number within
/// the stage, with the one lowercase letter of a step DESIGN.md inserts after it (`L1.39a`), and
/// a short lowercase description, joined by underscores (`l01_07_fences`, `l01_39a_bit_words`).
pub fn is_step_name(name: &str) -> bool {
    let mut parts = name.splitn(3, '_');
    let (Some(stage), Some(step), Some(desc)) = (parts.next(), parts.next(), parts.next()) else {
        return false;
    };
    let stage_ok = stage == "m0"
        || stage == "s"
        || (stage.len() == 3
            && stage.starts_with('l')
            && stage[1..]
                .parse::<u8>()
                .is_ok_and(|n| (1..=LAST_LAYER).contains(&n)));
    let digits = step
        .strip_suffix(|c: char| c.is_ascii_lowercase())
        .unwrap_or(step);
    let step_ok = digits.len() == 2
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.parse::<u8>().is_ok_and(|n| n >= 1);
    let desc_ok = !desc.is_empty()
        && !desc.starts_with('_')
        && !desc.ends_with('_')
        && desc
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_');
    stage_ok && step_ok && desc_ok
}

#[cfg(test)]
mod tests {
    use super::is_step_name;

    #[test]
    fn accepts_the_three_stage_kinds() {
        assert!(is_step_name("m0_01_scaffolding"));
        assert!(is_step_name("l01_07_fences"));
        assert!(is_step_name("l29_03_lowering_in_zed"));
        assert!(is_step_name("l30_01_editor"));
        assert!(is_step_name("l40_01_layout"));
        assert!(is_step_name("s_01_stage1"));
        assert!(is_step_name("l01_39a_bit_words"));
    }

    #[test]
    fn rejects_malformed_names() {
        for bad in [
            "m0_1_scaffolding", // step not two digits
            "l1_07_fences",     // layer not two digits
            "l41_01_beyond",    // no layer 41
            "l99_01_beyond",    // no layer 99
            "l00_01_zero",      // no layer 0
            "l01_00_zero",      // steps count from 1
            "l01_07",           // no description
            "l01_07_",          // empty description
            "l01_07_Fences",    // uppercase
            "x01_07_fences",    // unknown stage
            "l01_39ab_two",     // two letters after the step
            "l01_39A_upper",    // uppercase letter after the step
            "l01_00a_zero",     // steps count from 1
            "l01_3a_short",     // step not two digits
        ] {
            assert!(!is_step_name(bad), "{bad} was accepted");
        }
    }
}

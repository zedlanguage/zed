//! Shared helpers for the step tests in `tests/steps/`.
//!
//! Each step of DESIGN.md Part G has one folder, `tests/steps/<step>/`, holding that step's
//! tests and the Zed fixtures they read; golden outputs are `insta` snapshots in the folder's
//! `snapshots/` directory, accepted with `cargo insta review` (docs/layout.md).

use std::path::PathBuf;

/// The folder that holds every step folder.
pub fn steps_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("steps")
}

/// Whether `name` is a well-formed step-folder name: a stage (`m0`, `l01`…`l29`, or `s` for
/// the self-hosting row), the two-digit step number within the stage, and a short lowercase
/// description, joined by underscores (`l01_07_fences`).
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
                .is_ok_and(|n| (1..=29).contains(&n)));
    let step_ok = step.len() == 2 && step.parse::<u8>().is_ok_and(|n| n >= 1);
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
        assert!(is_step_name("s_01_stage1"));
    }

    #[test]
    fn rejects_malformed_names() {
        for bad in [
            "m0_1_scaffolding", // step not two digits
            "l1_07_fences",     // layer not two digits
            "l30_01_beyond",    // no layer 30
            "l00_01_zero",      // no layer 0
            "l01_00_zero",      // steps count from 1
            "l01_07",           // no description
            "l01_07_",          // empty description
            "l01_07_Fences",    // uppercase
            "x01_07_fences",    // unknown stage
        ] {
            assert!(!is_step_name(bad), "{bad} was accepted");
        }
    }
}

//! FAIL-steps-name-layers, found by TEST-complete-m0 (author P189): `is_step_name` accepted the
//! layers L1 to L29 only, from when L29 was the last layer.

use zed_tests::is_step_name;

/// DESIGN.md has layers L1 to L40 (`### L40 — a browser layout engine in Zed`), and a step's
/// tests live in `tests/steps/lNN_SS_description` (`tests/steps/l22_08_vacuity/`), so a step of
/// layers L30 to L40 needs a folder name with stage `l30` to `l40`.
#[test]
fn every_layer_of_design_names_a_step_folder() {
    for name in ["l30_01_editor", "l33_01_libraries", "l40_01_layout"] {
        assert!(is_step_name(name), "{name} is well named");
    }
    // No layer past the last one DESIGN.md has.
    assert!(!is_step_name("l41_01_x"), "l41 has no layer");
}

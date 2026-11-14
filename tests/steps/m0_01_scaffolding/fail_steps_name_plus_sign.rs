//! FAIL-steps-name-plus-sign, found by TEST-complete-m0 (author P189): `is_step_name` read the
//! layer with `parse::<u8>`, which accepts a leading `+`.

use zed_tests::is_step_name;

/// A stage is `m0`, `s` or `l01`…`lNN`: `l` and two digits. `l+1` is `l` and a sign and one
/// digit, so it names no layer; the step part already refuses `+1`.
#[test]
fn a_layer_with_a_sign_is_not_a_stage() {
    assert!(!is_step_name("l+1_01_a"), "l+1 is not a layer");
    assert!(!is_step_name("m0_+1_a"), "+1 is not a step");
}

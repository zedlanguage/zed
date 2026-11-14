use zed_tests::scaling;

use super::super::Resolved;
use super::super::given::helpers;

#[test]
fn many_helpers_narrowing_what_a_use_gives_scale() {
    let n = 200;
    let units: Vec<(usize, Resolved)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, Resolved::new(&helpers(m))))
        .collect();
    scaling::check("n helpers narrowing what a use gives", n, |m| {
        let (_, r) = units.iter().find(|(k, _)| *k == m).unwrap();
        let info = r.check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

//! The benchmarks of step L1.25: each scaling check and each control of the preimage catalog,
//! at `n` and `8n`, its inputs built before the timing. They run apart from the correctness
//! tests (`tools/run_tests.sh --bench`); each file's correctness tests check the same terms at
//! small sizes.

mod constant_minus;
mod deep;
mod overflow;
mod powers;
mod ref_memo;
mod s22;
mod scaling;
mod shared;
mod stops;

//! The benchmarks of `live3.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::live3::*;
use crate::scaling::decides;
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::live3::{Row3, point};
use zedc::store::presburger::satisfiable;

#[test]
fn many_rows_scale_linearly() {
    // Coefficients up to 50; the work is O(m log m), from `twovar::point` on each plane.
    let fifty = |rng: &mut Rng| int(rng.int(-50, 50));
    let (small, large) = (thin(410, 7, fifty), thin(410 * scaling::FACTOR, 7, fifty));
    scales("rows over three variables", 410, 1, &small, &large);
}

#[test]
fn slabs_of_million_coefficients_scale() {
    // The empty slab c·x = 1 of `parity_slabs_are_decided`, c = (10^6 + 1, 10^6 + 3, 10^6 + 5),
    // over the cube |x_i| <= 5, and m rows more with coefficients up to 50, each holding the
    // whole cube with slack 0 to 5, so no row bound settles it. Every stage runs over all the
    // rows: the linear programs, the rounding, LLL (the flat direction is c) and `twovar` on the
    // one plane c·x = 1, which has no point in the cube. The work is O(m log m). The linear
    // programs make O(m) calls of `Lin2::minus` (each round of `solve2` pairs its pieces and drops
    // a sixteenth or more), so their count is held to linear growth: measured 4,645 → 38,315 calls
    // from 192 to 1,536 rows, 8.25 times. The count does not depend on the load, so besides the
    // limit of 10.5 every scaling test meets it is held to 9 (`scaling::hold_linear`), the ratio
    // the author strongly prefers: at 9 an extra factor of log m (8 · log 1,536 / log 192 = 11.2)
    // fails, and so does an all-pairs pass of `Lin2::minus` in each round of `solve2`, which at
    // this size stays under the limit of the instruction count (COMPLEXITY.md S18).
    let c = [1_000_001, 1_000_003, 1_000_005];
    let family = |m: usize| -> Vec<Row3> {
        let mut rng = Rng::new(11);
        let mut rows: Vec<Row3> = [slab(c, 1, 0), cube(5)].concat();
        for _ in 0..m {
            let a = [0; 3].map(|_| rng.int(-50, 50));
            // The least of a·x over the cube is -5 Σ|a_i|.
            let least = -5 * a.iter().map(|c| c.abs()).sum::<i64>();
            rows.push(row(a, rng.int(0, 5) - least));
        }
        rows
    };
    let n = 192;
    let (small, large) = (family(n), family(n * scaling::FACTOR));
    scaling::hold_linear(
        &format!(
            "`Lin2::minus` over a slab of million coefficients: {n} and {} rows",
            n * scaling::FACTOR
        ),
        "calls",
        minus_calls(&small),
        minus_calls(&large),
    );
    scales(
        "rows over a slab of million coefficients",
        n,
        1,
        &small,
        &large,
    );
}

#[test]
fn a_lens_of_tangent_planes_away_from_the_origin_scales() {
    // Over (5000, 5000) no point of the box stage holds the lens, so `satisfiable` reaches
    // `live3`. From 128 to 1,024 pairs of planes: 1,489M to 7,163M instructions (4.8 times),
    // 57.9M to 399M bytes (6.9 times). With the removed `hull3` stage first it was 894M to
    // 11,712M (13.1 times) and 324M to 4,205M bytes (HULL3-subsumed, load 47 to 53).
    let f = formula(&tangents(64, 5_000));
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?}");
    decides(
        "a lens of tangent planes away from the origin",
        380,
        Ok(true),
        |n| formula(&tangents(n, 5_000)),
    );
}

#[test]
fn a_lens_of_tangent_planes_scales_in_point() {
    // With no integer point, every size takes the whole path of `point`: six linear programs,
    // the reduction and the slices. The lens alone over the origin is no scaling test of
    // `point`: there the rounded first vertex holds the rows at 128 pairs, which ends `point`
    // after one linear program on numbers that fit in 128 bits, and at 512 and 1,024 pairs it
    // does not, so `point` runs five and three linear programs, the later ones along
    // directions with 12 to 23 digits on numbers that do not fit (LIVE3-lp-tangents: 0.35 s,
    // 13.0 s and 7.3 s; 41.6 times the bytes from 128 to 1,024). The work of each linear
    // program was linear there: 35k to 345k pieces visited by `solve1` from 128 to 1,024.
    let (small, large) = (
        lens_in_a_thin_slab(70),
        lens_in_a_thin_slab(70 * scaling::FACTOR),
    );
    scaling::check(
        "a lens of tangent planes in a thin slab, in `point`",
        70,
        |m| {
            let rows = if m == 70 { &small } else { &large };
            std::hint::black_box(point(rows));
        },
    );
}

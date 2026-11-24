//! The rows [`super::solve`] reads, and the point it rebuilds from a value of the variable. They
//! are written here, not in `scaled.rs`, so that `sumset.rs`, which `scaled.rs` calls, names
//! nothing of `scaled.rs` and the files form no import cycle (test `s_01f_import_graph`).

use super::super::*;

/// A top-level equation read as the definition of a remainder and a quotient:
/// `r = (a * t + k) mod m` and `q = sigma * floor((a * t + k) / m)`, where `t` is the variable or
/// the quotient of another row. A row with no remainder atom (`r` is `None`) says the remainder
/// is zero.
pub(super) struct DefRow<'f> {
    pub(super) con: &'f Con,
    pub(super) a: Int,
    pub(super) k: Int,
    pub(super) m: Int,
    pub(super) q: Atom,
    pub(super) sigma: i8,
    pub(super) r: Option<Atom>,
    /// The row whose quotient is `t`, or `None` when `t` is the variable; [`super::solve`]
    /// declines a formula with any row that has one.
    pub(super) parent: Option<usize>,
}

/// A part of a [`SumRow`]: the variable, or the quotient or the remainder of row `i`.
#[derive(Clone, Copy)]
pub(super) enum Part {
    X,
    Q(usize),
    R(usize),
}

/// A top-level equation `sum_j c_j p_j + c_q q + c_r r + k0 == 0` (or with no `r`) whose parts
/// `p_j` are the variable and quotients and remainders of rows on it, read as
/// `r = E mod m` and `q = sigma * floor(E / m)` with `E = s (sum_j c_j p_j + k0)`, `s = -c_r`
/// (`1` with no remainder, which then says `E mod m = 0`), `m = |c_q|` and
/// `sigma = -sgn(s c_q)`. The proof is that of [`super::def_row`] with `A t` replaced by
/// `s sum_j c_j p_j`, which nothing in it reads beyond being an integer at each point.
/// `parts` holds `s c_j`, `k` holds `s k0`.
pub(super) struct SumRow {
    pub(super) parts: Vec<(Part, Int)>,
    pub(super) k: Int,
    pub(super) m: Int,
    pub(super) q: Atom,
    pub(super) sigma: i8,
    pub(super) r: Option<Atom>,
}

/// `E` of `sum` at the values `model` of the rows' parts (from [`point_at`]); `x` is the
/// variable's value. O(parts) arithmetic operations.
pub(super) fn sum_value(sum: &SumRow, rows: &[DefRow<'_>], model: &Model, x: &Int) -> Int {
    let mut e = sum.k.clone();
    for (p, k) in &sum.parts {
        let v = match p {
            Part::X => x,
            Part::Q(i) => &model[&rows[*i].q],
            Part::R(i) => &model[rows[*i].r.as_ref().expect("a remainder part has its atom")],
        };
        e = &e + &(k * v);
    }
    e
}

/// The interval of values in `0..m` at which the one-term constraint `c` on a remainder holds.
pub(super) fn remainder_values(c: &Con, m: &Int) -> ResidueSet {
    let (_, k) = c.lin.terms.iter().next().expect("one term");
    let c0 = &c.lin.constant;
    let (lo, hi) = match c.rel {
        Rel::Ge if k.is_positive() => ((-c0).div_ceil(k), m - &Int::ONE),
        Rel::Ge => (Int::ZERO, c0.div_floor(&-k)),
        Rel::Eq if c0.mod_floor(&k.abs()).is_zero() => {
            let v = (-c0).div_floor(k);
            (v.clone(), v)
        }
        Rel::Eq => return Vec::new(),
    };
    res_normalize(vec![(lo, hi)], m)
}

/// [`point_at`], and the quotient and remainder of each sum at `x = v` as [`SumRow`] reads them.
pub(super) fn point_with_sums(rows: &[DefRow<'_>], sums: &[SumRow], x: &Atom, v: &Int) -> Model {
    let mut model = point_at(rows, x, v);
    for sum in sums {
        let e = sum_value(sum, rows, &model, v);
        let fl = e.div_floor(&sum.m);
        if let Some(r) = &sum.r {
            model.insert(r.clone(), &e - &(&sum.m * &fl));
        }
        model.insert(sum.q.clone(), if sum.sigma > 0 { fl } else { -&fl });
    }
    model
}

/// The values at `x = v` of `x` and of each quotient and remainder its row (a row on `x`)
/// defines, as in (2) of the proof of [`super::solve`]: `E = a x + k`, `r = E mod m`,
/// `q = sigma * floor(E / m)`. O(rows) arithmetic operations.
pub(super) fn point_at(rows: &[DefRow<'_>], x: &Atom, v: &Int) -> Model {
    let mut model = Model::new();
    model.insert(x.clone(), v.clone());
    for row in rows {
        let e = &(&row.a * v) + &row.k;
        let fl = e.div_floor(&row.m);
        if let Some(r) = &row.r {
            model.insert(r.clone(), &e - &(&row.m * &fl));
        }
        let q = if row.sigma > 0 { fl } else { -&fl };
        model.insert(row.q.clone(), q);
    }
    model
}

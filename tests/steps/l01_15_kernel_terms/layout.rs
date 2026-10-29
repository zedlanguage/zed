//! The printer's line breaking: a term that fits stays on one line, one that does not puts
//! each part on its own line, and the text differs from the one-line form only in whitespace.

use zed_kernel::print::pretty;
use zed_kernel::term::build::{app, if_, lam, let_, lit, var};
use zed_kernel::{Prim, Term};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zed_tests::kernel::*;

/// The weekly revenue per region: a fold over a reindex over a filter.
fn revenue() -> Term {
    let sale = |f: &str| get(var("s"), lit(f));
    fold_at(
        reindex(
            discard(var("sales"), lam(&["s"], eq(sale("week"), var("week")))),
            lam(&["k", "s"], path(vec![sale("region"), var("k")])),
            lam(&["k", "s"], mul(sale("qty"), sale("price"))),
        ),
        2,
        Term::PrimFn(Prim::Add),
        Some(lit(0)),
    )
}

#[test]
fn a_term_that_fits_stays_on_one_line() {
    let t = revenue();
    let flat = t.to_string();
    assert_eq!(pretty(&t, flat.len()), flat);
    assert_eq!(pretty(&t, 1000), flat);
}

#[test]
fn a_term_that_does_not_fit_breaks_into_indented_parts() {
    assert_eq!(
        pretty(&revenue(), 60),
        "\
fold(
  reindex(
    discard(sales, s -> (get(s, \"week\") == week)),
    (k, s) -> path(get(s, \"region\"), k),
    (k, s) -> (get(s, \"qty\") * get(s, \"price\")),
    witness: residue
  ),
  (+),
  identity: 0,
  depth: 2,
  ev: {}
)"
    );
}

#[test]
fn every_line_fits_when_the_parts_do() {
    let t = revenue();
    for width in [40, 50, 60, 80] {
        let text = pretty(&t, width);
        let longest = text.lines().map(str::len).max().unwrap();
        assert!(longest <= width, "width {width}:\n{text}");
    }
}

#[test]
fn a_block_and_its_branches_break_inside_their_braces() {
    let t = let_(
        "subtotal",
        mul(var("quantity"), var("unitPrice")),
        if_(
            le(var("subtotal"), lit(100)),
            var("subtotal"),
            app(var("discounted"), vec![var("subtotal"), lit(10)]),
        ),
    );
    assert_eq!(
        pretty(&t, 40),
        "\
{
  subtotal = (quantity * unitPrice);
  if (subtotal <= 100) {
    subtotal
  } else {
    discounted(subtotal, 10)
  }
}"
    );
}

/// A random term over every generator, `depth` levels deep.
fn random(rng: &mut Rng, depth: usize) -> Term {
    let names = ["orders", "k", "v", "total", "région"];
    if depth == 0 {
        return match rng.below(3) {
            0 => var(rng.pick(&names)),
            1 => lit(rng.int(-50, 50)),
            _ => lit("a b"),
        };
    }
    let mut part = || random(rng, depth - 1);
    let (a, b, c) = (part(), part(), part());
    match rng.below(12) {
        0 => fam(a, "i", b),
        1 => reindex(a, b, c),
        2 => discard(a, b),
        3 => fold(a, b, Some(c)),
        4 => fix_lattice(a, b, c),
        5 => fix_defined(a, |this, k| app(this, vec![sub(k, b)])),
        6 => Term::Gen {
            init: rc(a),
            step: rc(b),
            guard: rc(c),
            pos: zed_kernel::GuardPos::After,
        },
        7 => let_("x", a, if_(b, c, var("x"))),
        8 => app(lam(&["x", "y"], a), vec![b, c]),
        9 => Term::Push("stdout".into(), rc(a)),
        10 => Term::Match(
            rc(a),
            vec![
                (zed_kernel::Pattern::Wild, b),
                (zed_kernel::Pattern::Bind("y".into()), c),
            ],
        ),
        _ => add(a, mul(b, c)),
    }
}

fn no_space(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn the_broken_text_is_the_flat_text_up_to_whitespace() {
    let mut rng = Rng::new(15);
    for _ in 0..RANDOM_INSTANCES {
        let depth = 1 + rng.below(4);
        let t = random(&mut rng, depth);
        let flat = t.to_string();
        assert!(!flat.contains('\n'), "{flat}");
        let width = 10 + rng.below(80);
        let text = pretty(&t, width);
        assert_eq!(no_space(&text), no_space(&flat), "width {width}:\n{text}");
        // Breaking only adds lines: a line break replaces a space or follows an opener, and
        // each broken line is indented by an even number of spaces.
        for line in text.lines() {
            let indent = line.len() - line.trim_start().len();
            assert_eq!(indent % 2, 0, "{text}");
        }
    }
}

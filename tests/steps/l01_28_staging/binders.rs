//! Row TEST-reads-deep-sharing: staging's binder list (`subs` in zedc-stage) names, form by
//! form, the names the kernel binds over each part (kernel `term::walk::kids`, the
//! evaluator). `stage::free` and `mix` both read it, and a staged term reaches more than the
//! kernel's `eval`: the native back end lowers it (`zed_native::through`), and mutation
//! testing skips a mutant whose mixed term equals the original's (`zedc::mutate`). A name
//! taken as bound where the kernel does not bind it lets `mix` drop the `let` that binds it,
//! which each of those reads wrongly; so the list is checked here part by part, not only
//! through one run.

use zed_kernel::term::build::{lit, var};
use zed_kernel::{Evidence, FixKind, GuardPos, Pattern, Prim, Shared, Term, Witness};
use zedc::stage::free;

/// A form built from its parts, and for each part whether the form binds `x` over it.
struct Form {
    name: &'static str,
    build: fn(Vec<Shared>) -> Term,
    bound: &'static [bool],
}

fn forms() -> Vec<Form> {
    fn fix(p: Vec<Shared>, this: &str, key: &str, kind: FixKind) -> Term {
        Term::Fix {
            init: p[0].clone(),
            step: p[1].clone(),
            this: this.into(),
            key: key.into(),
            kind,
            ev: Evidence::new(),
        }
    }
    vec![
        Form {
            name: "lambda",
            build: |p| Term::Lam(vec!["x".into()], p[0].clone()),
            bound: &[true],
        },
        Form {
            name: "call",
            build: |p| Term::App(p[0].clone(), vec![Term::clone(&p[1])]),
            bound: &[false, false],
        },
        Form {
            name: "primitive",
            build: |p| Term::Prim(Prim::Tuple, vec![Term::clone(&p[0]), Term::clone(&p[1])]),
            bound: &[false, false],
        },
        Form {
            name: "let",
            build: |p| Term::Let("x".into(), p[0].clone(), p[1].clone()),
            bound: &[false, true],
        },
        Form {
            name: "if",
            build: |p| Term::If(p[0].clone(), p[1].clone(), p[2].clone()),
            bound: &[false, false, false],
        },
        Form {
            name: "match",
            build: |p| {
                Term::Match(
                    p[0].clone(),
                    vec![
                        (Pattern::Bind("x".into()), Term::clone(&p[1])),
                        (Pattern::Wild, Term::clone(&p[2])),
                    ],
                )
            },
            bound: &[false, true, false],
        },
        Form {
            name: "fam",
            build: |p| Term::Fam {
                domain: p[0].clone(),
                var: "x".into(),
                body: p[1].clone(),
            },
            bound: &[false, true],
        },
        Form {
            name: "reindex",
            build: |p| Term::Reindex {
                family: p[0].clone(),
                kf: p[1].clone(),
                vf: p[2].clone(),
                witness: Witness::Residue,
            },
            bound: &[false, false, false],
        },
        Form {
            name: "discard",
            build: |p| Term::Discard {
                family: p[0].clone(),
                sel: p[1].clone(),
            },
            bound: &[false, false],
        },
        Form {
            name: "fold",
            build: |p| Term::Fold {
                family: p[0].clone(),
                op: p[1].clone(),
                identity: Some(p[2].clone()),
                depth: 1,
                ev: Evidence::new(),
            },
            bound: &[false, false, false],
        },
        Form {
            name: "definedness fix, `this` named x",
            build: |p| fix(p, "x", "k", FixKind::Definedness),
            bound: &[false, true],
        },
        Form {
            name: "definedness fix, `key` named x",
            build: |p| fix(p, "t", "x", FixKind::Definedness),
            bound: &[false, true],
        },
        Form {
            name: "lattice fix, `this` and `key` named x",
            build: |p| {
                let join = p[2].clone();
                fix(p, "x", "x", FixKind::Lattice { join })
            },
            bound: &[false, false, false],
        },
        Form {
            name: "gen",
            build: |p| Term::Gen {
                init: p[0].clone(),
                step: p[1].clone(),
                guard: p[2].clone(),
                pos: GuardPos::After,
            },
            bound: &[false, false, false],
        },
        Form {
            name: "push",
            build: |p| Term::Push("p".into(), p[0].clone()),
            bound: &[false],
        },
    ]
}

/// For each form and each of its parts, the form with `x` read in that part alone: `x` is
/// free exactly when the kernel does not bind it over the part. Seen to fail with `subs`
/// putting `this` and `key` over a lattice fix's step and join again (the fault of row
/// STAGE-subs-lattice-fix-names) and with a `fam` binding its key over its domain.
#[test]
fn staging_binds_over_each_part_of_every_form_the_names_the_kernel_binds() {
    for form in forms() {
        for (i, &bound) in form.bound.iter().enumerate() {
            let parts = (0..form.bound.len())
                .map(|j| Shared::new(if j == i { var("x") } else { lit(0i64) }))
                .collect();
            let t = (form.build)(parts);
            let free: Vec<String> = free(&t).iter().map(|x| x.to_string()).collect();
            let want: &[&str] = if bound { &[] } else { &["x"] };
            assert_eq!(free, want, "{}, `x` read in part {i}: {t:?}", form.name);
        }
    }
}

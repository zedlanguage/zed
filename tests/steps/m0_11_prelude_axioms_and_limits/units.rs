//! Unit addresses: an invoicing unit exports `total` and `tax`, with a local helper `rate` that
//! `tax` uses and a local `note` that nothing uses. Its address follows its exports' values and
//! nothing else.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Prim;
use zed_kernel::term::build::{lam, lit, prim, var};
use zed_kernel::term::{Evidence, Term};
use zedc::address::ContentAddress;
use zedc::canon::{Def, address, unit_address};

fn def(name: &str, body: Term) -> Def {
    Def {
        name: name.into(),
        domain: None,
        facets: vec![],
        body,
    }
}

/// The unit's declarations, `rate` as given and `line` naming each line in `total`.
fn invoicing(rate: i64, line: &str) -> Vec<Def> {
    let total = Term::Fold {
        family: Arc::new(Term::Fam {
            domain: Arc::new(var("lines")),
            var: line.into(),
            body: Arc::new(prim(
                Prim::Mul,
                vec![
                    prim(Prim::Get, vec![var(line), lit("qty")]),
                    prim(Prim::Get, vec![var(line), lit("price")]),
                ],
            )),
        }),
        op: Arc::new(Term::PrimFn(Prim::Add)),
        identity: Some(Arc::new(lit(0))),
        depth: 1,
        ev: Evidence::new(),
    };
    let tax = lam(
        &["amount"],
        prim(
            Prim::IntDiv,
            vec![prim(Prim::Mul, vec![var("amount"), var("rate")]), lit(100)],
        ),
    );
    vec![
        def("rate", lit(rate)),
        def("note", lit("prices in cents")),
        def("total", total),
        def("tax", tax),
    ]
}

/// The address of the unit whose declarations are `defs`, in dependency order, exporting
/// `exports`.
fn unit(defs: &[Def], exports: &[&str]) -> ContentAddress {
    let mut known: BTreeMap<String, ContentAddress> = BTreeMap::new();
    for d in defs {
        let a = address(d, &|x| known.get(x).copied());
        known.insert(d.name.to_string(), a);
    }
    let out: Vec<(&str, ContentAddress)> = exports.iter().map(|e| (*e, known[*e])).collect();
    unit_address(&out)
}

const EXPORTS: [&str; 2] = ["total", "tax"];

#[test]
fn the_address_is_pinned() {
    // Any change to this value is a change to every unit's address, so it goes with a new
    // canonicalization VERSION.
    assert_eq!(
        unit(&invoicing(8, "line"), &EXPORTS).to_string(),
        "f59b01a226a8aa9dffe695c452c6daf4274c7160aa447522ace60cefd8b32f8a"
    );
}

#[test]
fn local_names_and_export_order_do_not_change_it() {
    let a = unit(&invoicing(8, "line"), &EXPORTS);
    assert_eq!(a, unit(&invoicing(8, "row"), &EXPORTS));
    assert_eq!(a, unit(&invoicing(8, "line"), &["tax", "total"]));
}

#[test]
fn a_changed_local_helper_changes_it_through_the_export_that_uses_it() {
    let a = unit(&invoicing(8, "line"), &EXPORTS);
    assert_ne!(a, unit(&invoicing(9, "line"), &EXPORTS));
    // The unused `note` reaches no export.
    let mut noted = invoicing(8, "line");
    noted[1] = def("note", lit("prices in euros"));
    assert_eq!(a, unit(&noted, &EXPORTS));
    // Exporting it does change the address.
    assert_ne!(a, unit(&invoicing(8, "line"), &["total", "tax", "note"]));
}

#[test]
fn the_arrows_of_an_overloaded_name_are_all_hashed() {
    let show = |s: &str| address(&def("show", lam(&["x"], lit(s))), &|_| None);
    let (a, b) = (show("int"), show("bool"));
    let both = unit_address(&[("show", a), ("show", b)]);
    assert_eq!(both, unit_address(&[("show", b), ("show", a)]));
    assert_ne!(both, unit_address(&[("show", a)]));
}

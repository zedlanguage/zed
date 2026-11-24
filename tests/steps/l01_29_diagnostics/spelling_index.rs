//! Step L1.29e: the spelling index (DESIGN.md sec:diagnostics, "Nearest in spelling";
//! zed-collections `spelling::nearest`, where the method, its proof and its complexity comment
//! are). Each case below is one of the step's test. The places are the positions of a unit's
//! text: a name is visible from its declaration to the end of its scope, `from..to`.

use zed_collections::spelling::nearest;

/// Each kind of slip finds the name: a deleted character (`Confg`), an inserted one
/// (`Configg`), a replaced one (`Cinfig`), two adjacent ones swapped (`Cofnig`); and the folded
/// spelling, `my_var` offering `myVar`.
#[test]
fn each_kind_of_slip_offers_the_name() {
    let names = [("Config", 0..100), ("myVar", 0..100)];
    let written = [
        ("Confg", 50),
        ("Configg", 50),
        ("Cinfig", 50),
        ("Cofnig", 50),
        ("my_var", 50),
    ];
    let config = Some("Config");
    assert_eq!(
        nearest(&names, &written),
        [config, config, config, config, Some("myVar")]
    );
}

/// With two near names, the first in name order is offered, whichever was declared first.
#[test]
fn of_two_near_names_the_first_in_name_order_is_offered() {
    let names = [("Configs", 0..100), ("Config", 10..100)];
    assert_eq!(nearest(&names, &[("Confign", 50)]), [Some("Config")]);
    let names = [("Config", 0..100), ("Configs", 10..100)];
    assert_eq!(nearest(&names, &[("Confign", 50)]), [Some("Config")]);
}

/// With none near, two slips away, no name is offered.
#[test]
fn two_slips_away_no_name_is_offered() {
    let names = [("Config", 0..100)];
    assert_eq!(nearest(&names, &[("Cofnigg", 50)]), [None]);
}

/// A name declared after the site, or in a scope that does not enclose it, is not offered; the
/// same name in a scope that encloses a later site is.
#[test]
fn a_name_not_visible_at_the_site_is_not_offered() {
    // `width` is declared at 60, after the site 50; `height` is a parameter of a function at
    // 10..40, a scope that does not enclose 50 but does enclose 20.
    let names = [("width", 60..100), ("height", 10..40)];
    let written = [("widht", 50), ("hieght", 50), ("hieght", 20), ("widht", 70)];
    assert_eq!(
        nearest(&names, &written),
        [None, None, Some("height"), Some("width")]
    );
}

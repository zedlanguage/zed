//! Which keys a partial arrow bounds when the keys are atoms of one name with other payloads.

use zedc::check::read::parse_type;

/// An overload of partial arrows bounds a function's values only at the keys of each arrow
/// (DESIGN.md sec:type_language), so a function whose keys are all `#t(bool)` is one of
/// `(#t(int) ->? #a) & (#t(bool) ->? int)`: no key of it is a `#t(int)`. Before
/// (FAIL-types-partial-arrow-same-atom-keys), `Ty::meets` read two payloads of one atom as
/// sharing a value whatever the payloads, and the arrow over `#t(bool)` was taken as one that
/// may take a key of `#t(int)`; with keys of two atoms or two scalars the answer was already
/// yes. The last two cases are neighbors that must stay refused: payloads that share a value.
#[test]
fn a_partial_arrow_over_another_payload_of_one_atom_bounds_no_key_of_it() {
    let cases = [
        ("#t(bool) ->? int", "(#t(int) ->? #a) & (#t(bool) ->? int)"),
        (
            "#t((bool, bool)) ->? int",
            "(#t((int, int)) ->? #a) & (#t((bool, bool)) ->? int)",
        ),
        ("#t(bool) ->? int", "(#u(int) ->? #a) & (#t(bool) ->? int)"),
        ("bool ->? int", "(int ->? #a) & (bool ->? int)"),
    ];
    for (s, q) in cases {
        let (s_t, q_t) = (parse_type(s).unwrap(), parse_type(q).unwrap());
        assert!(s_t.subtype(&q_t), "`{s}` is not found within `{q}`");
    }
    let refused = [
        (
            "#t(bool | int) ->? int",
            "(#t(int) ->? #a) & (#t(bool) ->? int)",
        ),
        (
            "#t((bool, int)) ->? int",
            "(#t((int | bool, int)) ->? #a) & (#t((bool, int)) ->? int)",
        ),
    ];
    for (s, q) in refused {
        let (s_t, q_t) = (parse_type(s).unwrap(), parse_type(q).unwrap());
        assert!(!s_t.subtype(&q_t), "`{s}` is found within `{q}`");
    }
}

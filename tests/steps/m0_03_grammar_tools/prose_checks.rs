//! The checks `sync` runs on the spec's prose (`zed_tools::spec_checks`): the kernel's rule names
//! that no message prints, and each way the prelude laws can disagree with DESIGN.md. The build
//! modes check is tested with the step that added it (l07_03_unit_log_off/modes.rs).

use zed_tests::step_helpers::m0_03_grammar_tools::KERNEL;
use zed_tools::spec_checks::{kernel_rules, prelude_laws};

#[test]
fn the_kernel_rules_are_the_generators_and_every_t_rule_the_spec_names() {
    let kernel = format!("Intro.\n{KERNEL}");
    let design = format!(
        "Intro: T-Var and xT-Not and T-lower.\n{KERNEL}\n# (sec:categories) Next\nT-App.\n"
    );
    let generators = [
        "Boom",
        "T-Discard",
        "T-Fam",
        "T-Fix",
        "T-Fold",
        "T-Gen",
        "T-Port",
        "T-Reindex",
    ];
    let got = kernel_rules(&design).expect("seven generators");
    let mut want = generators.to_vec();
    want.extend(["T-App", "T-Var"]);
    want.sort();
    assert_eq!(got, want);

    // Lines that are no generator: no `(`, an upper-case name, a name with a non-word
    // character.
    let skipped = kernel.replace(
        "    | port(decl)\n",
        "    | port(decl)\n    | nothing\n    | Big(x)\n    | a-b(x)\n",
    );
    assert_eq!(
        kernel_rules(&skipped),
        Ok(generators.map(String::from).to_vec())
    );
    // A generator in a later section is not read.
    let after = format!("{kernel}\n# (sec:categories) Next\n    | extra(x)\n");
    assert_eq!(
        kernel_rules(&after),
        Ok(generators.map(String::from).to_vec())
    );

    let six = kernel.replace("    | port(decl)\n", "");
    assert_eq!(
        kernel_rules(&six),
        Err("sec:kernel's grammar has 6 generators, not seven or more".to_string())
    );
    assert_eq!(
        kernel_rules("no kernel\n"),
        Err("DESIGN.md has no section sec:kernel".to_string())
    );
}

#[test]
fn each_way_the_prelude_laws_disagree_is_named() {
    let laws = "`anyIntro`, `anyElim`, `allElim` and `allIntro`";
    let states = "The prelude also states `anyIntro`, `anyElim`, `allElim` and \
                  `law allIntro(p: P) -> Q`. More.\n";
    let step = format!("L15.7. Build the prelude laws {laws}; test: {laws} reach proof grade.\n");
    let page = "law allIntro(p: P) -> Q proof { done }\n";
    let good = format!("{step}{states}");
    assert_eq!(prelude_laws(&good, page), Ok(()));
    // A law stated as `law name(` counts as stated too.
    let by_law = good.replace(
        "`anyElim`, `allElim` and `law",
        "law anyElim(x), `allElim` and `law",
    );
    assert_eq!(prelude_laws(&by_law, page), Ok(()));

    let cases: [(String, &str, &str); 7] = [
        (states.to_string(), page, "DESIGN.md has no step L15.7"),
        (
            format!("L15.7. Build nothing.\n{states}"),
            page,
            "step L15.7 names no prelude laws",
        ),
        (
            good.replacen("`anyElim`, ", "", 1),
            page,
            "step L15.7 builds the prelude laws",
        ),
        (
            good.replace(" reach proof grade", ""),
            page,
            "step L15.7's test names no laws that reach proof grade",
        ),
        (
            good.replace("test: `anyIntro`, ", "test: "),
            page,
            "step L15.7's test brings",
        ),
        (
            step.clone(),
            page,
            "DESIGN.md does not state the prelude laws",
        ),
        (
            good.replace("states `anyIntro`, ", "states "),
            page,
            "DESIGN.md does not state `anyIntro`",
        ),
    ];
    for (design, page, want) in cases {
        let got = prelude_laws(&design, page);
        assert!(
            got.as_ref().is_err_and(|e| e.starts_with(want)),
            "{design}\n{got:?}"
        );
    }
    let got = prelude_laws(&good, "law allIntro(p: P) -> Q\n");
    assert_eq!(
        got,
        Err("the mathlib study does not write `allIntro` with a proof".to_string())
    );
}

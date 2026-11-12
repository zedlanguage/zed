//! The two reads of `build`, and every other use, rejected naming them: an option the build
//! does not declare is rejected with the declared options listed, and a target literal that
//! names no target with the targets listed.

use zedc::build::Build;
use zedc::run::load_for;

/// The build for x86_64 Linux of a package that declares `declared`, with `on` turned on.
fn build(declared: &[&str], on: &[&str]) -> Build {
    let declared: Vec<String> = declared.iter().map(|o| o.to_string()).collect();
    Build::new("x86_64-linux", &declared, on).unwrap()
}

/// The report of the errors of `src` built for `b`.
fn rejected(src: &str, b: &Build) -> String {
    match load_for(src.as_bytes(), b) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(report) => report,
    }
}

/// The headlines of `report`: its lines that start with a place `l:c:`.
fn headlines(report: &str) -> Vec<&str> {
    report
        .lines()
        .filter(|l| {
            l.split(':')
                .next()
                .is_some_and(|n| n.parse::<u32>().is_ok())
        })
        .collect()
}

#[test]
fn an_undeclared_option_is_rejected_with_the_declared_options_in_manifest_order() {
    let src = "f() = if build.options.quick { 1 } else { 2 };\n";
    let report = rejected(src, &build(&["fast", "counting"], &[]));
    assert_eq!(
        headlines(&report),
        [
            "1:10: `build.options.quick` names no option: the package declares the options \
          `fast` and `counting`."
        ],
        "{report}"
    );
    // The repair is the manifest line with the option added at its end, the order kept.
    assert!(
        report.contains(
            "repair: declare it in the manifest `zed.manifest`, as \
             `options = \"fast, counting, quick\";`"
        ),
        "{report}"
    );
    // A declared option is read, on or off.
    let read = format!(
        "{}main(m: MainArgs) {{}}\n",
        src.replace("quick", "counting")
    );
    let p = load_for(read.as_bytes(), &build(&["fast", "counting"], &[]));
    assert!(p.is_ok(), "{:?}", p.err());
}

#[test]
fn an_option_read_where_the_package_declares_none_says_so() {
    let report = rejected("f() = build.options.fast;\n", &Build::default());
    assert_eq!(
        headlines(&report),
        ["1:7: `build.options.fast` names no option: the package declares no option."],
        "{report}"
    );
    assert!(report.contains("as `options = \"fast\";`"), "{report}");
}

#[test]
fn every_use_other_than_the_two_reads_is_rejected_naming_them() {
    let src = "a() = build;\n\
               b() = build.options;\n\
               c() = build.arch;\n\
               d() = build?.target;\n\
               e() = build.options?.fast;\n";
    let report = rejected(src, &build(&["fast"], &[]));
    let reads = "`build` is read as `build.target` or `build.options.<name>`";
    assert_eq!(
        headlines(&report),
        [
            format!("1:7: `build` alone is no value: {reads}."),
            format!("2:7: `build.options` alone is no value: {reads}, one option at a time."),
            format!("3:7: `build.arch`: `build` has no member `arch`: {reads}."),
            format!("4:7: `build?.target` reads no atom, so it takes `.`: {reads}."),
            format!("5:7: `build.options?.fast` reads no atom, so it takes `.`: {reads}."),
        ],
        "{report}"
    );
}

#[test]
fn a_target_literal_that_names_no_target_is_rejected_on_either_side() {
    let report = rejected(
        "f() = build.target == \"x86_64-linx\";\ng() = \"arm\" != build.target;\n",
        &Build::default(),
    );
    let targets = "`x86_64-linux`, `aarch64-linux`, `riscv64-linux`, `x86_64-macos`, \
                   `aarch64-macos`, `x86_64-windows` and `aarch64-windows`";
    assert_eq!(
        headlines(&report),
        [
            format!("1:23: `x86_64-linx` is no target: `build.target` is one of {targets}."),
            format!("2:7: `arm` is no target: `build.target` is one of {targets}."),
        ],
        "{report}"
    );
    // A target the build is not for is still a target: its branch is checked and dropped.
    assert!(
        load_for(
            "f() = \"aarch64-macos\" == build.target;\nmain(m: MainArgs) {}\n".as_bytes(),
            &Build::default()
        )
        .is_ok()
    );
}

#[test]
fn a_programs_own_build_shadows_the_word() {
    // Any member of the program's `build` is its own: no read is replaced and none rejected.
    let p = load_for(
        "build = \"mine\";\nf() = build;\nmain(m: MainArgs) { m.stdout <- f() ++ \"\\n\"; }\n"
            .as_bytes(),
        &build(&[], &[]),
    );
    assert!(p.is_ok(), "{:?}", p.err());
}

#[test]
fn a_read_is_a_literal_of_the_build() {
    let src = "main(m: MainArgs) {\n  m.stdout <- if build.options.fast { \"fast on\\n\" } \
               else { \"fast off\\n\" };\n}\n";
    for (on, kept, cut) in [
        (&["fast"][..], "fast on", "fast off"),
        (&[][..], "fast off", "fast on"),
    ] {
        let zir = super::lowered(src, &build(&["fast"], on), true);
        assert!(zir.contains(kept) && !zir.contains(cut), "{on:?}:\n{zir}");
    }
}

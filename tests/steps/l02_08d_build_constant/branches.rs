//! A program reading the constant lowers each target's branch only.

use zedc::build::Build;
use zedc::run::load_for;

/// A program with a branch for each of two targets and one for the rest.
const BY_TARGET: &str = "main(m: MainArgs) {
  m.stdout <- if build.target == \"x86_64-linux\" {
    \"x86_64 branch\\n\"
  } else if build.target == \"aarch64-linux\" {
    \"aarch64 branch\\n\"
  } else {
    \"other branch\\n\"
  };
}
";

/// The ZIR `src` lowers to when built for `build`, staged first when `staged`.
pub(crate) fn lowered(src: &str, build: &Build, staged: bool) -> String {
    let p = load_for(src.as_bytes(), build).unwrap_or_else(|e| panic!("{src}: {e}"));
    let p = if staged { p.stage().0 } else { p };
    let g = zedc::zir::lower::lower(&p.term()).unwrap_or_else(|e| panic!("{src}: {e}"));
    zedc::zir::text::print(&g)
}

fn build(target: &str) -> Build {
    Build::new(target, &[], &[]).unwrap()
}

#[test]
fn each_target_lowers_its_own_branch_only() {
    for (target, kept) in [
        ("x86_64-linux", "x86_64 branch"),
        ("aarch64-linux", "aarch64 branch"),
        ("riscv64-linux", "other branch"),
    ] {
        let zir = lowered(BY_TARGET, &build(target), true);
        for branch in ["x86_64 branch", "aarch64 branch", "other branch"] {
            assert_eq!(
                zir.contains(branch),
                branch == kept,
                "built for {target}, the branch `{branch}`:\n{zir}"
            );
        }
    }
}

#[test]
fn without_staging_every_branch_is_lowered() {
    // The control: the reads are literals, and only the build's evaluation drops a branch.
    let zir = lowered(BY_TARGET, &build("x86_64-linux"), false);
    for branch in ["x86_64 branch", "aarch64 branch", "other branch"] {
        assert!(zir.contains(branch), "{branch}:\n{zir}");
    }
}

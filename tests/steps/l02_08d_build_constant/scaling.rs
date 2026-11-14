//! The reads are replaced in time linear in the program, up to the logarithm of the uses map:
//! n and 8n reads in one tuple, so that the reads are most of the work of the front end. The
//! benchmark in `bench/scaling.rs` holds the time; here a few reads pass the front end.

use zedc::build::Build;

/// A unit of one definition, a tuple of `n` reads, the target and an option in turn.
pub(super) fn reads(n: usize) -> String {
    let mut text = String::from("f() = (");
    for i in 0..n {
        text += if i % 2 == 0 {
            "build.target == \"x86_64-linux\", "
        } else {
            "build.options.fast, "
        };
    }
    text + ");\n"
}

/// The build the reads are for: the target they name, with the option `fast` turned on.
pub(super) fn fast_build() -> Build {
    Build::new("x86_64-linux", &["fast".to_string()], &["fast"]).unwrap()
}

/// The front end over `reads(n)` gives no error.
pub(super) fn front_passes(build: &Build, n: usize) {
    let text = reads(n);
    let mut db = zedc::query::Db::for_build(build.clone());
    if let Err(e) = &*db.front(&text) {
        panic!("{:?}", e.first().map(|e| &e.message));
    }
}

#[test]
fn a_few_reads_pass_the_front_end() {
    let build = fast_build();
    for n in [0, 1, 2, 9] {
        front_passes(&build, n);
    }
}

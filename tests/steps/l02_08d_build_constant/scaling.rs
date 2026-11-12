//! The reads are replaced in time linear in the program, up to the logarithm of the uses map:
//! n and 8n reads in one tuple, so that the reads are most of the work of the front end.

use zedc::build::Build;

/// A unit of one definition, a tuple of `n` reads, the target and an option in turn.
fn reads(n: usize) -> String {
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

#[test]
fn reads_scale_linearly() {
    let build = Build::new("x86_64-linux", &["fast".to_string()], &["fast"]).unwrap();
    zed_tests::scaling::check_order("the front end over n reads of `build`", 2000, 1, |n| {
        let text = reads(n);
        let mut db = zedc::query::Db::for_build(build.clone());
        if let Err(e) = &*db.front(&text) {
            panic!("{:?}", e.first().map(|e| &e.message));
        }
    });
}

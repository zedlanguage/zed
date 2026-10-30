//! The object writer shares the JIT's generator: the object file of a graph exports
//! `zed_root`, imports the runtime's hooks, and is the same bytes on every build.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};

use super::planned;

fn program() -> zed_kernel::Term {
    let f = lam(&["x"], prim(Prim::Concat, vec![var("x"), lit("!")]));
    let_("f", f, app(var("f"), vec![lit("hi")]))
}

fn contains(hay: &[u8], needle: &str) -> bool {
    hay.windows(needle.len()).any(|w| w == needle.as_bytes())
}

#[test]
fn the_object_file_is_reproducible_and_names_its_symbols() {
    let (g, p) = planned(&program());
    let a = zed_native::object(&g, &p).unwrap();
    let b = zed_native::object(&g, &p).unwrap();
    assert_eq!(a, b);
    for sym in ["zed_root", "rt_node", "rt_inc", "rt_dec", "rt_register"] {
        assert!(contains(&a, sym), "{sym}");
    }
    assert!(!contains(&a, "rt_nonexistent"), "the search can fail");
    #[cfg(target_os = "linux")]
    assert_eq!(&a[..4], b"\x7fELF");
}

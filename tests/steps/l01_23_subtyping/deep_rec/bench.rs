//! The benchmarks of `deep_rec.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `deep_rec.rs`.

use super::*;
use zed_tests::scaling;

/// Which of the four measures a test takes.
#[derive(Clone, Copy)]
enum Measure {
    Copying,
    Comparing,
    Writing,
    Checking,
}

/// One measure of the body `shape` of `nested`, `n` and `8n` deep, on the 2 MiB stack of
/// `deep::on_small_stack`. Only that body is kept: `nested` builds all seven and the other six
/// are dropped at once, so that the peak holds one build of the seven at 8n, not four; the
/// second body `==` compares is a copy of the first, not a second build.
/// TEST-bench-move-l0123, author P169: this was one test making the 28 checks at n = 20,000
/// (`copying_comparing_writing_and_checking_scale_with_depth`, 20.7 s alone); each check is
/// now a test of its own, sized so that its run at 8n takes about 3 s, and at most 250,000
/// deep (150,000 for morphisms, the largest body) so that the peak stays under 6 GB.
fn scales(shape: &str, n: usize, measure: Measure) {
    zed_tests::deep::on_small_stack(|| {
        let one = |k: usize| {
            let (_, body) = nested(k, int)
                .into_iter()
                .find(|(what, _)| *what == shape)
                .expect("a shape of `nested`");
            let copy = match measure {
                Measure::Comparing => Some(body.clone()),
                _ => None,
            };
            (body, copy)
        };
        let (small, large) = (one(n), one(8 * n));
        let at = |k: usize| if k == n { &small } else { &large };
        match measure {
            Measure::Copying => scaling::check(&format!("copying {shape}"), n, |k| {
                drop(std::hint::black_box(at(k).0.clone()));
            }),
            Measure::Comparing => scaling::check(&format!("comparing {shape}"), n, |k| {
                let (a, b) = at(k);
                assert!(std::hint::black_box(Some(a) == b.as_ref()));
            }),
            Measure::Writing => {
                scaling::check(&format!("writing the Debug text of {shape}"), n, |k| {
                    std::hint::black_box(format!("{:?}", at(k).0));
                })
            }
            // The copy is linear, timed above.
            Measure::Checking => scaling::check(&format!("checking a body of {shape}"), n, |k| {
                assert!(Group::new(vec![def(at(k).0.clone())]).is_ok());
            }),
        }
    });
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 380000; 1x 94.7 ms at load 25.
#[test]
fn copying_a_deep_body_of_unions_scales() {
    scales("unions", 380000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 460000; 1x 22.2 ms at load 25.
#[test]
fn comparing_deep_bodies_of_unions_scales() {
    scales("unions", 460000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 160000; 1x 0.27 s at load 25.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_unions_scales() {
    scales("unions", 160000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 280000; 1x 0.42 s at load 24.
#[test]
fn checking_a_deep_body_of_unions_scales() {
    scales("unions", 280000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 0.11 s at load 24.
#[test]
fn copying_a_deep_body_of_intersections_scales() {
    scales("intersections", 500000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 63.9 ms at load 23.
#[test]
fn comparing_deep_bodies_of_intersections_scales() {
    scales("intersections", 500000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 200000; 1x 0.65 s at load 23.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_intersections_scales() {
    scales("intersections", 200000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 270000; 1x 0.26 s at load 24.
#[test]
fn checking_a_deep_body_of_intersections_scales() {
    scales("intersections", 270000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 97.8 ms at load 24.
#[test]
fn copying_a_deep_body_of_complements_scales() {
    scales("complements", 500000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 17.2 ms at load 24.
#[test]
fn comparing_deep_bodies_of_complements_scales() {
    scales("complements", 500000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 16.9 ms at load 24.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_complements_scales() {
    scales("complements", 500000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 330000; 1x 0.28 s at load 24.
#[test]
fn checking_a_deep_body_of_complements_scales() {
    scales("complements", 330000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 0.19 s at load 24.
#[test]
fn copying_a_deep_body_of_differences_scales() {
    scales("differences", 500000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 38.3 ms at load 24.
#[test]
fn comparing_deep_bodies_of_differences_scales() {
    scales("differences", 500000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 170000; 1x 0.34 s at load 24.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_differences_scales() {
    scales("differences", 170000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 200000; 1x 0.18 s at load 9.
#[test]
fn checking_a_deep_body_of_differences_scales() {
    scales("differences", 200000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 97.7 ms at load 26.
#[test]
fn copying_a_deep_body_of_tuples_scales() {
    scales("tuples", 500000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 19.0 ms at load 26.
#[test]
fn comparing_deep_bodies_of_tuples_scales() {
    scales("tuples", 500000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 17.5 ms at load 26.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_tuples_scales() {
    scales("tuples", 500000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 330000; 1x 0.17 s at load 9.
#[test]
fn checking_a_deep_body_of_tuples_scales() {
    scales("tuples", 330000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 0.17 s at load 27.
#[test]
fn copying_a_deep_body_of_atoms_scales() {
    scales("atoms", 500000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 500000; 1x 37.3 ms at load 27.
#[test]
fn comparing_deep_bodies_of_atoms_scales() {
    scales("atoms", 500000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 200000; 1x 0.31 s at load 9.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_atoms_scales() {
    scales("atoms", 200000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 260000; 1x 0.29 s at load 27.
#[test]
fn checking_a_deep_body_of_atoms_scales() {
    scales("atoms", 260000, Measure::Checking);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 300000; 1x 0.21 s at load 27.
#[test]
fn copying_a_deep_body_of_morphisms_scales() {
    scales("morphisms", 300000, Measure::Copying);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 300000; 1x 35.8 ms at load 27.
#[test]
fn comparing_deep_bodies_of_morphisms_scales() {
    scales("morphisms", 300000, Measure::Comparing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 97000; 1x 0.31 s at load 26.
#[test]
fn writing_the_debug_text_of_a_deep_body_of_morphisms_scales() {
    scales("morphisms", 97000, Measure::Writing);
}

/// TEST-bench-move-l0123, author P169: n was 20,000, now 150000; 1x 0.50 s at load 26.
#[test]
fn checking_a_deep_body_of_morphisms_scales() {
    scales("morphisms", 150000, Measure::Checking);
}

// The three tests below were regular tests of `deep_rec.rs`, moved here as they were
// (TEST-bench-move-l0123, author P178: a test that needs an unusual depth or stack is a
// benchmark); each has a small instance there, at depth `DEPTH` on the default test thread.

/// The depth of the deep bodies: twice the depth near which the derived `Clone`, `==` and
/// `Debug`, and the recursive checks, overflowed the 2 MiB stack of `deep::on_small_stack`
/// (near 10,000 levels).
const DEEP: usize = 20_000;

/// The bodies of `nested` from `first` to `last` (in its order), `DEEP` deep, are copied,
/// compared, written and admitted on a 2 MiB stack.
fn shapes_on_a_small_stack(first: &str, last: &str) {
    zed_tests::deep::on_small_stack(|| {
        let other = nested(DEEP, || Expr::Type(Type::string()));
        let all = nested(DEEP, int)
            .into_iter()
            .zip(nested(DEEP, int))
            .zip(other);
        let from = all.skip_while(|(((what, _), _), _)| *what != first);
        let mut seen = 0;
        for (((what, a), (_, b)), (_, c)) in from {
            seen += 1;
            let copy = a.clone();
            assert!(copy == a, "{what}: a copy equals its original");
            assert!(a == b, "{what}: two builds are equal");
            assert!(a != c, "{what}: a different bottom is found");
            let text = format!("{a:?}");
            assert_eq!(text, format!("{copy:?}"), "{what}");
            assert!(text.len() > DEEP, "{what}: {} bytes", text.len());
            assert!(Group::new(vec![def(a)]).is_ok(), "{what}");
            if what == last {
                break;
            }
        }
        assert!(seen > 0, "no shape from {first} to {last}");
    });
}

// The body test ran all seven shapes and the two recursive occurrences at depth 100,000 in one
// test (5.2 s alone); now it runs them at depth `DEEP`, 20,000, twice the depth its comment
// gave for the overflow of the 2 MiB stack, in two tests, the first four shapes and then the
// other three with the recursive occurrences (TEST-bench-move-l0123, author P169: a deep-stack
// test uses the smallest depth that still overflows the stack in the code it guards against).

#[test]
fn a_body_far_deeper_than_the_stack_is_copied_compared_written_and_checked() {
    shapes_on_a_small_stack("unions", "differences");
}

#[test]
fn a_deep_body_of_tuples_atoms_or_morphisms_is_copied_compared_written_and_checked() {
    shapes_on_a_small_stack("tuples", "morphisms");
    zed_tests::deep::on_small_stack(|| {
        // A recursive occurrence `DEEP` constructors down is contractive; one under `DEEP`
        // complements is not monotone.
        let guarded = (0..DEEP).fold(Expr::Ref(0, vec![]), |e, _| Expr::Tuple(vec![e]));
        assert!(Group::new(vec![def(Expr::Union(vec![guarded, int()]))]).is_ok());
        let flipped = (0..DEEP).fold(Expr::Tuple(vec![Expr::Ref(0, vec![])]), |e, _| {
            Expr::Not(Box::new(e))
        });
        assert!(Group::new(vec![def(flipped)]).is_err());
    });
}

/// Round 8 (X39): a deep type kept only by the thread's emptiness tables is freed when the
/// thread ends. `forget_emptiness` uses those tables before the thread makes any type, so they
/// were dropped after the queue that frees types in a loop, and the type was freed by
/// recursion: `r6two` at `n` 4096 overflowed a 256 MiB stack so.
///
/// It freed a tuple 100,000 deep on a 1 MiB stack (1.8 s alone); now it frees one 20,000 deep
/// on a 256 KiB stack (TEST-bench-move-l0123, author P169: the smallest depth that still
/// overflows the stack in the code it guards against). Every level of a free by recursion is
/// at least one call, and a call keeps at least 16 bytes of stack on x86-64 (the return address
/// and the 16-byte alignment of the stack at a call), so 20,000 levels need at least 320,000
/// bytes, more than the 262,144 of the stack, whatever the size of the frames.
#[test]
fn a_deep_type_kept_by_the_verdicts_is_freed_when_its_thread_ends() {
    scaling::on_a_thread(1 << 18, || {
        Type::forget_emptiness();
        let t = (0..20_000).fold(Type::int(), |t, _| Type::tuple(vec![t, Type::int()]));
        assert_eq!(t.verdict(), zed_kernel::types::Verdict::Inhabited);
    });
}

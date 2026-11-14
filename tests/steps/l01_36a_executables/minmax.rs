//! A program of `min`, `max` and `clamp` on floats read from its command line, built into an
//! executable, prints the interpreter's lines on every triple of the corner values: IEEE
//! 754-2019 `minimum` and `maximum` (DESIGN.md sec:reduction, item 5) in both argument orders,
//! and `clamp(x, lo, hi) = max(lo, min(x, hi))`, the values known only when the program runs.

use std::ffi::OsString;

use zed_kernel::Value;

use super::{built, dir, executable, interpreter};

const MINMAX: &str = "\
clamp(positional x, positional lo, positional hi) { max(lo, min(x, hi)) }

main(m: MainArgs) {
  x = f64(m.args[0] else \"\") else 0.0;
  y = f64(m.args[1] else \"\") else 0.0;
  z = f64(m.args[2] else \"\") else 0.0;
  m.stdout <- \"${min(x, y)} ${min(y, x)} ${max(x, y)} ${max(y, x)} ${clamp(x, y, z)}\";
}
";

/// The corner values as the program reads them.
const CORNERS: [&str; 7] = ["nan", "-0.0", "0.0", "inf", "-inf", "1.0", "-1.0"];

/// IEEE 754-2019 `minimum` (`min` true) or `maximum`, as the standard states it.
fn ieee(min: bool, a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a != b {
        if (a < b) == min { a } else { b }
    } else if a.is_sign_negative() == min {
        a
    } else {
        b
    }
}

#[test]
fn min_max_and_clamp_on_floats_agree_with_the_interpreter() {
    let d = dir("minmax");
    let src = d.join("minmax.zed");
    std::fs::write(&src, MINMAX).unwrap();
    let exe = d.join("minmax");
    built(&src, &exe);
    let show = |x: f64| Value::float(x).to_string();
    // Each run is a process of the executable and a whole `zedc run`, 686 in all, so each
    // value of x takes a thread of its own: the same triples in a seventh of the time.
    let n: usize = std::thread::scope(|scope| {
        let threads: Vec<_> = CORNERS
            .map(|x| {
                let (src, exe) = (&src, &exe);
                scope.spawn(move || {
                    let mut n = 0;
                    for y in CORNERS {
                        for z in CORNERS {
                            let words: Vec<OsString> =
                                vec!["--".into(), x.into(), y.into(), z.into()];
                            let native = executable(exe, &words, b"");
                            assert_eq!(native, interpreter(src, &words, b""), "{x} {y} {z}");
                            let [a, b, c] = [x, y, z].map(|s| s.parse::<f64>().unwrap());
                            let want = format!(
                                "{} {} {} {} {}\n",
                                show(ieee(true, a, b)),
                                show(ieee(true, b, a)),
                                show(ieee(false, a, b)),
                                show(ieee(false, b, a)),
                                show(ieee(false, b, ieee(true, a, c))),
                            );
                            assert_eq!((native.status, native.stdout), (0, want), "{x} {y} {z}");
                            n += 1;
                        }
                    }
                    n
                })
            })
            .into();
        threads.into_iter().map(|t| t.join().unwrap()).sum()
    });
    assert_eq!(n, 343);
}

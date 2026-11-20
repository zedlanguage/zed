//! The unit whose address the tests of TEST-param-digest-pinned pin, shared by the step's own
//! test binary (`digest_pin.rs`) and the test of the `zedc` executable (`pins_binary.rs`, a
//! target of zed-native, which includes this file by path).

/// The unit `u`: each export's type holds function types whose parameter names a call may
/// write, at each place the address keeps them (ADDR-nested-param-names): a returned function
/// (`p`), a parameter's function type (`apply`), a tuple of functions, one of which takes a
/// function (`both`), and a union of three functions (`pick`), whose order in the type is the
/// order the checker adds them in.
pub const UNIT: &str = "\
p(k: f64) {
  g(z: f64) = z * k;
  return g;
}
apply(f: (x: f64) -> f64) = f(x: 1.0);
both(s: f64) {
  g(a: f64) = a + s;
  h(b: (c: f64) -> f64) = b(c: s);
  return (g, h);
}
pick(positional t: int) {
  g(v: f64) = v;
  h(w: f64) = w * 2.0;
  j(y: f64) = y * 3.0;
  return if t == 0 { g } else { if t == 1 { h } else { j } };
}
";

/// The address of [`UNIT`], strings written as their bytes (author answer A106, 2026-11-20). The
/// address is a BLAKE3 hash of byte strings whose layout is fixed (little-endian counts, names
/// by their UTF-8 bytes), so it is the same in every process and on every machine; it changes
/// with each change to the serialization, and is pinned again then.
pub const ADDRESS: &str = "a6164229eefd1f7e10e6c4ae6c9a233fea8245b424ec1894209e2d01a3b35cca";

/// The units beside `u` in the package of the batch run: `a` checks function types of the same
/// shapes before `u` is reached, and `b` imports `u` too, so `u` is checked in a process that has
/// made many other types first.
pub const OTHERS: [(&str, &str); 2] = [
    (
        "a.zed",
        "twice(f: (y: f64) -> f64) {\n  g(q: f64) = f(y: f(y: q));\n  return g;\n}\n\
         pair(r: f64) {\n  g(z: f64) = z * r;\n  h(x: f64) = x + r;\n  return (h, g);\n}\n",
    ),
    (
        "b.zed",
        "import u;\nscale(n: f64) {\n  g(w: f64) = w * n;\n  return (g, g);\n}\n",
    ),
];

/// The main unit of the batch run: it imports `a`, `b` and `u`, in that order.
pub const BATCH_MAIN: &str = "import a;\nimport b;\nimport u;\nmain(m: MainArgs) {}\n";

/// The main unit of the single-file run: it imports `u` alone.
pub const SINGLE_MAIN: &str = "import u;\nmain(m: MainArgs) {}\n";

//! Step S.7b, row CLIF-shim: every C function of the shim `zed-clif`, called from Rust through
//! its C interface (an `extern "C"` block naming the exported symbols, so each call goes through
//! the C calling convention as the Zed compiler's will), with the row's corner cases and the
//! scaling test.

#![expect(
    unsafe_code,
    reason = "calls the shim's C functions, which are `unsafe` to call"
)]

/// The scaling test of the rule of low complexity, shared with the step tests.
#[path = "../../src/scaling.rs"]
#[expect(dead_code, reason = "this test uses only some of the shared checks")]
mod scaling;

// The meter's `malloc` in this test binary, which `scaling` measures each run with
// (`zed_alloc_count::metered`, TEST-meter-allocator-bias).
zed_alloc_count::meter_entry_points!();

use zed_clif::{ZedClifBytes, ZedClifRelocation};

/// A target handle, opaque, as a C caller declares it.
#[repr(C)]
struct ZedClifTarget {
    _opaque: [u8; 0],
}

/// A code image, opaque, as a C caller declares it.
#[repr(C)]
struct ZedClifImage {
    _opaque: [u8; 0],
}

/// An error, opaque, as a C caller declares it.
#[repr(C)]
struct ZedClifError {
    _opaque: [u8; 0],
}

// The shim's C interface, declared as a C caller declares it, with the handles opaque. The Rust
// declarations in `zed_clif` are not called: only these are; the two `#[repr(C)]` structures
// passed by value are the crate's own.
unsafe extern "C" {
    fn zed_clif_target_new(
        name: ZedClifBytes,
        flags: ZedClifBytes,
        error: *mut *mut ZedClifError,
    ) -> *mut ZedClifTarget;
    fn zed_clif_target_free(target: *mut ZedClifTarget);
    fn zed_clif_generate(
        target: *const ZedClifTarget,
        clif: ZedClifBytes,
        symbols: *const ZedClifBytes,
        symbol_count: usize,
        error: *mut *mut ZedClifError,
    ) -> *mut ZedClifImage;
    fn zed_clif_image_free(image: *mut ZedClifImage);
    fn zed_clif_image_function_count(image: *const ZedClifImage) -> usize;
    fn zed_clif_image_name(image: *const ZedClifImage, index: usize) -> ZedClifBytes;
    fn zed_clif_image_code(image: *const ZedClifImage, index: usize) -> ZedClifBytes;
    fn zed_clif_image_code_alignment(image: *const ZedClifImage, index: usize) -> u32;
    fn zed_clif_image_relocation_count(image: *const ZedClifImage, index: usize) -> usize;
    fn zed_clif_image_relocation(
        image: *const ZedClifImage,
        index: usize,
        reloc: usize,
        out: *mut ZedClifRelocation,
    ) -> bool;
    fn zed_clif_error_text(error: *const ZedClifError) -> ZedClifBytes;
    fn zed_clif_error_free(error: *mut ZedClifError);
}

/// The x86-64 Linux target every test but `host_target` uses, so the expected relocations do
/// not depend on the machine the tests run on.
const X86_64: &str = "x86_64-unknown-linux-gnu";

/// A byte string the shim reads, for `s`.
fn bytes(s: &str) -> ZedClifBytes {
    ZedClifBytes {
        ptr: s.as_ptr(),
        len: s.len(),
    }
}

/// The bytes of `b`, which the shim returned and which are still valid.
fn read(b: ZedClifBytes) -> Vec<u8> {
    if b.ptr.is_null() {
        assert_eq!(b.len, 0, "a null pointer with a length");
        return Vec::new();
    }
    // SAFETY: the shim returned `b` from an image or error not yet released.
    unsafe { std::slice::from_raw_parts(b.ptr, b.len) }.to_vec()
}

/// The text of `b`, which the shim returned.
fn text(b: ZedClifBytes) -> String {
    String::from_utf8(read(b)).expect("the shim returns UTF-8 text")
}

/// Takes the error the shim stored in `error`: its text, and releases it.
fn take_error(error: *mut ZedClifError) -> String {
    assert!(!error.is_null(), "a call that failed set no error");
    // SAFETY: an error from the shim, released once, here.
    unsafe {
        let t = text(zed_clif_error_text(error));
        zed_clif_error_free(error);
        t
    }
}

/// The target `name` with `flags`, or the error's text.
fn target(name: &str, flags: &str) -> Result<*mut ZedClifTarget, String> {
    let mut error = std::ptr::null_mut();
    // SAFETY: the byte strings live through the call; `error` is writable.
    let t = unsafe { zed_clif_target_new(bytes(name), bytes(flags), &mut error) };
    if t.is_null() {
        Err(take_error(error))
    } else {
        assert!(error.is_null(), "a call that succeeded set an error");
        Ok(t)
    }
}

/// One relocation, its names copied out of the image.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Reloc {
    offset: u32,
    addend: i64,
    kind: String,
    symbol: String,
}

/// One function of an image, copied out of it through every reader.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Function {
    name: String,
    code: Vec<u8>,
    alignment: u32,
    relocations: Vec<Reloc>,
}

/// Every function of `image`, read through each reader; checks the readers' answers past the
/// last function and relocation.
fn read_image(image: *const ZedClifImage) -> Vec<Function> {
    // SAFETY: a live image; `out` is writable.
    unsafe {
        let count = zed_clif_image_function_count(image);
        let functions = (0..count)
            .map(|f| {
                let n = zed_clif_image_relocation_count(image, f);
                let relocations = (0..n)
                    .map(|r| {
                        let mut out = std::mem::MaybeUninit::<ZedClifRelocation>::uninit();
                        assert!(zed_clif_image_relocation(image, f, r, out.as_mut_ptr()));
                        let out = out.assume_init();
                        Reloc {
                            offset: out.offset,
                            addend: out.addend,
                            kind: text(out.kind),
                            symbol: text(out.symbol),
                        }
                    })
                    .collect();
                let mut out = std::mem::MaybeUninit::<ZedClifRelocation>::uninit();
                assert!(!zed_clif_image_relocation(image, f, n, out.as_mut_ptr()));
                assert!(!zed_clif_image_relocation(
                    image,
                    f,
                    0,
                    std::ptr::null_mut()
                ));
                Function {
                    name: text(zed_clif_image_name(image, f)),
                    code: read(zed_clif_image_code(image, f)),
                    alignment: zed_clif_image_code_alignment(image, f),
                    relocations,
                }
            })
            .collect();
        // Past the last function: the empty answers.
        assert!(zed_clif_image_name(image, count).ptr.is_null());
        assert!(zed_clif_image_code(image, count).ptr.is_null());
        assert_eq!(zed_clif_image_code_alignment(image, count), 0);
        assert_eq!(zed_clif_image_relocation_count(image, count), 0);
        functions
    }
}

/// Generates `clif` for `target` with `symbols`: the functions read out of the image, which is
/// then released, or the error's text.
fn generate(
    target: *const ZedClifTarget,
    clif: &str,
    symbols: &[&str],
) -> Result<Vec<Function>, String> {
    let names: Vec<ZedClifBytes> = symbols.iter().map(|s| bytes(s)).collect();
    let mut error = std::ptr::null_mut();
    // SAFETY: `target` is live; the text and names live through the call; `error` is writable.
    let image = unsafe {
        zed_clif_generate(
            target,
            bytes(clif),
            if names.is_empty() {
                std::ptr::null()
            } else {
                names.as_ptr()
            },
            names.len(),
            &mut error,
        )
    };
    if image.is_null() {
        return Err(take_error(error));
    }
    assert!(error.is_null(), "a call that succeeded set an error");
    let functions = read_image(image);
    // SAFETY: the image, released once, here.
    unsafe { zed_clif_image_free(image) };
    Ok(functions)
}

/// Generates `clif` for the x86-64 target with `symbols`.
fn generate_x86(clif: &str, symbols: &[&str]) -> Result<Vec<Function>, String> {
    let t = target(X86_64, "").expect("the x86-64 target");
    let result = generate(t, clif, symbols);
    // SAFETY: the target, released once, here.
    unsafe { zed_clif_target_free(t) };
    result
}

/// A function that calls an external function `u0:1` and reads the address of a symbol `u0:2`.
const CALL_AND_SYMBOL: &str = "
function u0:0(i64) -> i64 {
    sig0 = (i64) -> i64
    fn0 = u0:1 sig0
    gv0 = symbol u0:2

block0(v0: i64):
    v1 = call fn0(v0)
    v2 = symbol_value.i64 gv0
    v3 = iadd v1, v2
    return v3
}
";

/// The names of [`CALL_AND_SYMBOL`]'s `u0:0`, `u0:1` and `u0:2`.
const NAMES: [&str; 3] = ["caller", "callee", "data"];

#[test]
fn a_call_and_a_symbol_give_one_relocation_each_named_as_in_the_text() {
    let functions = generate_x86(CALL_AND_SYMBOL, &NAMES).expect("the function compiles");
    assert_eq!(functions.len(), 1);
    let f = &functions[0];
    assert_eq!(f.name, "caller");
    assert!(!f.code.is_empty());
    assert!(f.alignment.is_power_of_two(), "alignment {}", f.alignment);
    let mut symbols: Vec<&str> = f.relocations.iter().map(|r| r.symbol.as_str()).collect();
    symbols.sort_unstable();
    assert_eq!(
        symbols,
        ["callee", "data"],
        "relocations {:?}",
        f.relocations
    );
    for r in &f.relocations {
        assert!(
            usize::try_from(r.offset).expect("a u32 offset") < f.code.len(),
            "relocation {r:?} past the code's {} bytes",
            f.code.len()
        );
        assert!(!r.kind.is_empty());
    }
}

/// A function with one argument and result of type `ty` that returns its argument.
fn identity(name: &str, ty: &str) -> String {
    format!("function %{name}({ty}) -> {ty} {{\nblock0(v0: {ty}):\n    return v0\n}}\n")
}

#[test]
fn malformed_text_gives_an_error_naming_the_line() {
    let e = generate_x86("function %f( {\n", &[]).expect_err("malformed text");
    assert!(e.starts_with("the CLIF text, line 1"), "{e}");
    let e = generate_x86("\n\nfunction %f() {\nblock0:\n    v0 = nonsense\n}\n", &[])
        .expect_err("an unknown instruction");
    assert!(e.starts_with("the CLIF text, line 5"), "{e}");
}

#[test]
fn a_function_that_fails_the_verifier_gives_an_error_naming_it() {
    // Returns an i32 where the signature says i64: the parser accepts it, the verifier does not.
    let bad = "function %wrong(i32) -> i64 {\nblock0(v0: i32):\n    return v0\n}\n";
    let e = generate_x86(bad, &[]).expect_err("a type error");
    assert!(e.starts_with("wrong: "), "{e}");
    assert!(e.contains("i64"), "{e}");
    // With the verifier setting off, the shim still verifies the function itself.
    let t = target(X86_64, "enable_verifier=false").expect("the target");
    let e = generate(t, bad, &[]).expect_err("a type error, verified by the shim");
    assert!(e.starts_with("wrong: "), "{e}");
    // SAFETY: released once.
    unsafe { zed_clif_target_free(t) };
}

#[test]
fn the_same_text_gives_the_same_bytes() {
    let text = format!("{CALL_AND_SYMBOL}{}", identity("second", "i32"));
    let first = generate_x86(&text, &NAMES).expect("compiles");
    let second = generate_x86(&text, &NAMES).expect("compiles");
    assert_eq!(first.len(), 2);
    assert_eq!(first, second);
    // And with one target handle used twice.
    let t = target(X86_64, "").expect("the target");
    let (a, b) = (generate(t, &text, &NAMES), generate(t, &text, &NAMES));
    // SAFETY: released once.
    unsafe { zed_clif_target_free(t) };
    assert_eq!(a.expect("compiles"), first);
    assert_eq!(b.expect("compiles"), first);
}

#[test]
fn an_empty_text_gives_an_image_with_no_functions() {
    for text in ["", "\n  \n", "; a comment and nothing else\n"] {
        assert_eq!(generate_x86(text, &[]), Ok(Vec::new()), "{text:?}");
    }
}

#[test]
fn a_function_with_no_blocks_gives_an_error() {
    // Cranelift 0.137.1 panics on it; the shim reports it before compiling.
    let e = generate_x86("function %empty() {\n}\n", &[]).expect_err("no blocks");
    assert_eq!(e, "empty: the function has no blocks");
}

#[test]
fn a_panic_in_cranelift_gives_an_error_and_the_shim_still_works() {
    // Cranelift 0.137.1 panics ("i128 args/return values not supported unless LLVM ABI
    // extensions are enabled", isa/x64/abi.rs) on an i128 argument for x86-64 with its default
    // settings, rather than returning an error; the shim catches it at its entry.
    let e = generate_x86(&identity("wide", "i128"), &[]).expect_err("a panic");
    assert!(
        e.starts_with("internal error in Cranelift or the shim: "),
        "{e}"
    );
    assert!(e.contains("i128"), "{e}");
    // The process and the shim go on: the same text with the setting compiles.
    let t = target(X86_64, "enable_llvm_abi_extensions").expect("the target");
    let wide = generate(t, &identity("wide", "i128"), &[]);
    // SAFETY: released once.
    unsafe { zed_clif_target_free(t) };
    assert_eq!(wide.expect("compiles with the setting").len(), 1);
}

#[test]
fn an_unknown_target_gives_an_error() {
    let e = target("no-such-target", "").expect_err("not a triple");
    assert!(e.starts_with("the target `no-such-target`: "), "{e}");
    let e = target("mips-unknown-linux-gnu", "").expect_err("not supported");
    assert_eq!(
        e,
        "the target `mips-unknown-linux-gnu`: Cranelift does not support it"
    );
    let e = target("", "").expect_err("an empty name");
    assert!(e.starts_with("the target ``: "), "{e}");
}

#[test]
fn an_unknown_flag_or_a_bad_value_gives_an_error() {
    assert_eq!(
        target(X86_64, "no_such_flag=1").expect_err("unknown"),
        "the flag `no_such_flag=1`: no setting `no_such_flag`"
    );
    assert_eq!(
        target(X86_64, "no_such_flag").expect_err("unknown"),
        "the flag `no_such_flag`: no setting `no_such_flag`"
    );
    let e = target(X86_64, "opt_level=fastest").expect_err("a bad value");
    assert!(e.starts_with("the flag `opt_level=fastest`: "), "{e}");
    assert_eq!(
        target(X86_64, "opt_level").expect_err("no value"),
        "the flag `opt_level`: `opt_level` needs a value, `opt_level=<value>`"
    );
}

#[test]
fn shared_and_instruction_set_flags_are_accepted() {
    for flags in [
        "",
        "opt_level=speed is_pic",
        "has_avx2 has_sse41",
        "  is_pic\n",
    ] {
        let t = target(X86_64, flags).unwrap_or_else(|e| panic!("{flags:?}: {e}"));
        let f = generate(t, CALL_AND_SYMBOL, &NAMES);
        // SAFETY: released once.
        unsafe { zed_clif_target_free(t) };
        assert_eq!(f.expect("compiles").len(), 1, "{flags:?}");
    }
}

#[test]
fn the_host_target_compiles() {
    let t = target("host", "").expect("the host");
    let f = generate(t, CALL_AND_SYMBOL, &NAMES);
    // SAFETY: released once.
    unsafe { zed_clif_target_free(t) };
    let f = f.expect("compiles");
    assert_eq!(f.len(), 1);
    assert_eq!(f[0].relocations.len(), 2);
}

#[test]
fn a_released_handle_is_not_needed_by_its_image() {
    let t = target(X86_64, "").expect("the target");
    let mut error = std::ptr::null_mut();
    // SAFETY: the target is live; the text and names live through the call.
    let image = unsafe {
        let names: Vec<ZedClifBytes> = NAMES.iter().map(|s| bytes(s)).collect();
        let image = zed_clif_generate(t, bytes(CALL_AND_SYMBOL), names.as_ptr(), 3, &mut error);
        // The target is released, and not used again; the image does not need it.
        zed_clif_target_free(t);
        image
    };
    assert!(!image.is_null() && error.is_null());
    let functions = read_image(image);
    assert_eq!(functions[0].name, "caller");
    // SAFETY: released once; then null, which every release accepts.
    unsafe {
        zed_clif_image_free(image);
        zed_clif_target_free(std::ptr::null_mut());
        zed_clif_image_free(std::ptr::null_mut());
        zed_clif_error_free(std::ptr::null_mut());
    }
}

#[test]
fn null_and_bad_arguments_give_errors_or_empty_answers() {
    let mut error = std::ptr::null_mut();
    // SAFETY: each pointer is null or valid for the call.
    unsafe {
        // A null target.
        let image = zed_clif_generate(std::ptr::null(), bytes(""), std::ptr::null(), 0, &mut error);
        assert!(image.is_null());
        assert_eq!(take_error(error), "no target: the target handle is null");
        // A null error out-parameter: the call fails and writes nothing.
        let t = zed_clif_target_new(
            bytes("mips-unknown-linux-gnu"),
            bytes(""),
            std::ptr::null_mut(),
        );
        assert!(t.is_null());
        // A null pointer with a length.
        let missing = ZedClifBytes {
            ptr: std::ptr::null(),
            len: 3,
        };
        error = std::ptr::null_mut();
        assert!(zed_clif_target_new(missing, bytes(""), &mut error).is_null());
        assert_eq!(
            take_error(error),
            "the target: a null pointer with length 3"
        );
        let t = target(X86_64, "").expect("the target");
        error = std::ptr::null_mut();
        assert!(zed_clif_generate(t, bytes(""), std::ptr::null(), 2, &mut error).is_null());
        assert_eq!(
            take_error(error),
            "the symbols: a null pointer with 2 symbols"
        );
        // Text that is not UTF-8.
        let latin1 = *b"\xe9";
        error = std::ptr::null_mut();
        let not_utf8 = ZedClifBytes {
            ptr: latin1.as_ptr(),
            len: 1,
        };
        assert!(zed_clif_generate(t, not_utf8, std::ptr::null(), 0, &mut error).is_null());
        assert!(take_error(error).starts_with("the CLIF text: not UTF-8"));
        zed_clif_target_free(t);
        // The readers on a null image and error.
        let none = std::ptr::null();
        assert_eq!(zed_clif_image_function_count(none), 0);
        assert!(zed_clif_image_name(none, 0).ptr.is_null());
        assert!(zed_clif_image_code(none, 0).ptr.is_null());
        assert_eq!(zed_clif_image_code_alignment(none, 0), 0);
        assert_eq!(zed_clif_image_relocation_count(none, 0), 0);
        let mut out = std::mem::MaybeUninit::<ZedClifRelocation>::uninit();
        assert!(!zed_clif_image_relocation(none, 0, 0, out.as_mut_ptr()));
        let empty = zed_clif_error_text(std::ptr::null());
        assert!(empty.ptr.is_null() && empty.len == 0);
    }
}

#[test]
fn a_text_with_a_test_set_target_or_feature_line_gives_an_error() {
    for line in [
        "test compile",
        "set opt_level=speed",
        "target x86_64",
        "target aarch64",
        "feature \"experimental_x64\"",
    ] {
        let text = format!("; a comment\n{line}\n{}", identity("f", "i32"));
        let e = generate_x86(&text, &[]).expect_err(line);
        assert!(
            e.starts_with(&format!(
                "the CLIF text, line 2: `{line}` before the first function"
            )),
            "{e}"
        );
    }
    // A comment, a blank line, and the keyword written against the name are not such lines.
    let text = "; comment\n\nfunction%f(i32) -> i32 {\nblock0(v0: i32):\n    return v0\n}\n";
    assert_eq!(generate_x86(text, &[]).expect("compiles")[0].name, "f");
}

#[test]
fn names_resolve_by_the_symbols_and_out_of_range_names_give_errors() {
    // `u0:5` with three symbols.
    let e = generate_x86(&CALL_AND_SYMBOL.replace("u0:2", "u0:5"), &NAMES).expect_err("range");
    assert_eq!(e, "the name u0:5: there are 3 symbols, u0:0 to u0:2");
    // Namespace 1.
    let e = generate_x86(&CALL_AND_SYMBOL.replace("u0:1", "u1:1"), &NAMES).expect_err("ns");
    assert_eq!(
        e,
        "the name u1:1: only namespace 0 (`u0:<index>`) names symbols"
    );
    // No symbols at all: the function's own name `u0:0` has none.
    let e = generate_x86(CALL_AND_SYMBOL, &[]).expect_err("no symbols");
    assert_eq!(e, "the name u0:0: no symbol names were given");
    // A test-case name is its text; a call Cranelift makes on its own is the C library's name.
    let ceil = "function %round_up(f32) -> f32 {\nblock0(v0: f32):\n    v1 = ceil v0\n    \
                return v1\n}\n";
    let f = generate_x86(ceil, &[]).expect("compiles");
    assert_eq!(f[0].name, "round_up");
    let symbols: Vec<&str> = f[0].relocations.iter().map(|r| r.symbol.as_str()).collect();
    assert_eq!(symbols, ["ceilf"], "{:?}", f[0].relocations);
}

#[test]
fn constants_and_jump_tables_are_inside_the_code() {
    // A jump table: its entries are bytes of the code, with no relocation.
    let table = "function %pick(i32) -> i32 {\nblock0(v0: i32):\n    br_table v0, block1, \
                 [block2, block1, block2]\nblock1:\n    v1 = iconst.i32 1\n    return v1\n\
                 block2:\n    v2 = iconst.i32 2\n    return v2\n}\n";
    let f = generate_x86(table, &[]).expect("compiles");
    assert!(f[0].relocations.is_empty(), "{:?}", f[0].relocations);
    // A vector constant from the constant pool: the code's alignment covers the constant's.
    let vector = "function %four() -> i32x4 {\nblock0:\n    v0 = vconst.i32x4 [1 2 3 4]\n    \
                  return v0\n}\n";
    let f = generate_x86(vector, &[]).expect("compiles");
    assert!(f[0].relocations.is_empty(), "{:?}", f[0].relocations);
    assert!(f[0].alignment >= 16, "alignment {}", f[0].alignment);
    let constant: Vec<u8> = [1u32, 2, 3, 4]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
    assert!(
        f[0].code.windows(16).any(|w| w == constant.as_slice()),
        "the constant is not in the code {:?}",
        f[0].code
    );
}

/// A text of `n` functions `u0:0` to `u0:n-1`, each the same small loop with a call.
fn functions(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "function u0:{i}(i64) -> i64 {{\n    sig0 = (i64) -> i64\n    fn0 = u0:{n} sig0\n\
                 block0(v0: i64):\n    jump block1(v0)\nblock1(v1: i64):\n    \
                 v2 = call fn0(v1)\n    v4 = iconst.i64 {i}\n    v3 = iadd v2, v4\n    \
                 brif v3, block1(v3), block2\n\
                 block2:\n    return v3\n}}\n"
            )
        })
        .collect()
}

/// The names `f0` to `fn` that `functions(n)` defines and calls.
fn function_names(n: usize) -> Vec<String> {
    (0..=n).map(|i| format!("f{i}")).collect()
}

/// `n` functions generate `n` bodies, the last calling `fn`.
fn generates_each_function(text: &str, names: &[String], n: usize) {
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let f = generate_x86(text, &names).expect("compiles");
    assert_eq!(f.len(), n);
    assert_eq!(f[n - 1].relocations[0].symbol, format!("f{n}"));
}

/// The answers of `bench::generation_scales_with_the_number_of_functions` at small sizes
/// (BENCH-meters-outside-bench).
#[test]
fn generation_gives_each_function_at_small_sizes() {
    for n in [1, 2, 8] {
        generates_each_function(&functions(n), &function_names(n), n);
    }
}

/// The benchmark of generation, run by `tools/run_tests.sh --bench`.
mod bench {
    use super::*;

    #[test]
    fn generation_scales_with_the_number_of_functions() {
        // Parsing and compiling are per function, and every function here is the same size,
        // so the work is of order n in the number of functions. Each run makes and releases
        // its target, a cost that does not grow with n.
        let texts = scaling::inputs(40, |n| (functions(n), function_names(n)));
        scaling::check("zed_clif_generate of n functions", 40, |n| {
            let (text, names) = &texts[&n];
            generates_each_function(text, names, n);
        });
    }
}

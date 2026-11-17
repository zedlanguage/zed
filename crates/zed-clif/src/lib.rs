//! The Cranelift shim of DESIGN step S.7b: Cranelift's text form (CLIF) to machine code and
//! relocations, behind a set of C functions (`#[unsafe(no_mangle)] extern "C"`), for the Zed
//! compiler, which has no other way to call Cranelift: Cranelift has no C interface.
//!
//! The functions, in the order a caller uses them:
//!
//! - [`zed_clif_target_new`]: a target, by its name and its flags, to a target handle, or an
//!   error. [`zed_clif_target_free`] releases the handle.
//! - [`zed_clif_generate`]: a target handle, CLIF text and the symbol names, to a code image, or
//!   an error. The text is parsed by `cranelift-reader`, and each function in it is verified
//!   and compiled by `cranelift-codegen`, in the order of the text. [`zed_clif_image_free`]
//!   releases the image.
//! - Reading an image: [`zed_clif_image_function_count`], and for each function
//!   [`zed_clif_image_name`], [`zed_clif_image_code`], [`zed_clif_image_code_alignment`],
//!   [`zed_clif_image_relocation_count`] and [`zed_clif_image_relocation`].
//! - [`zed_clif_error_text`]: the text of an error. [`zed_clif_error_free`] releases it.
//!
//! **Read-only data.** Cranelift writes a function's constants (its constant pool) and its jump
//! tables into the same bytes as its instructions, after them, and reports no separate data: so
//! the code of a function, as [`zed_clif_image_code`] gives it, holds its read-only data too,
//! and the image has no other. The loader maps the code bytes as they are, aligned to
//! [`zed_clif_image_code_alignment`], which is at least the alignment of each constant.
//!
//! **Names.** A function's name and the targets of its relocations are text:
//!
//! - a user name `u0:i` is the `i`-th symbol name the caller passed to [`zed_clif_generate`];
//!   a user name in a namespace other than 0, or past the last symbol name, is an error;
//! - a test-case name `%name` is `name`, as written;
//! - a call to one of Cranelift's own library functions (`ceilf`, `memcpy` and the others it
//!   emits on its own) is the C name `cranelift_module::default_libcall_names` gives it, the
//!   name zed-native's code generator links by;
//! - a well-known symbol (`ElfGlobalOffsetTable`, `CoffTlsIndex`) is Cranelift's name for it.
//!
//! A relocation's kind is Cranelift's name for it (`Abs8`, `X86CallPCRel4`, `X86GOTPCRel4`,
//! `Aarch64AdrPrelPgHi21` and the others of `cranelift_codegen::binemit::Reloc`), its offset is
//! from the start of the function's code, and its addend is Cranelift's.
//!
//! **Errors and panics.** Every function catches a panic at its entry (`catch_unwind`); a
//! function that returns a handle or an image returns null and sets `*error` to an error that
//! holds the panic's message, and the other functions return their empty value. No panic leaves
//! the shim, so none can reach the C caller, where unwinding through a C frame would stop the
//! process. A panic message is still printed to standard error by the panic hook of the process
//! (Rust's default hook unless the program sets another); the shim does not change the hook,
//! since a hook is state of the whole process.
//!
//! **State.** The shim maps no memory and keeps no state between calls but the handles and
//! images it returns: each call reads only its arguments, and two calls with the same arguments
//! give the same bytes.
//!
//! **Pointers.** A byte string the caller passes is a [`ZedClifBytes`]; one with a null pointer
//! and length 0 is empty. A byte string the shim returns points into the handle, image or error
//! it came from and is valid until that is released. A null handle, image or error is accepted
//! everywhere and gives an error or the empty value; a pointer that is not null must be one the
//! shim returned and not yet released (each function's `# Safety` section).

// The lint fires on each C function three ways (`no_mangle`, `unsafe fn`, the block that reads
// the caller's pointers), so it is expected for the whole crate, which is a C interface and
// nothing else; each `unsafe` block carries its `// SAFETY:` comment.
#![expect(
    unsafe_code,
    reason = "a C interface: exported symbols and reads of the caller's pointers"
)]

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::str::FromStr;

use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::{ExternalName, Function, UserFuncName};
use cranelift_codegen::isa::{self, CallConv, LookupError, OwnedTargetIsa};
use cranelift_codegen::print_errors::{pretty_error, pretty_verifier_error};
use cranelift_codegen::settings::{self, Configurable, SetError};
use cranelift_codegen::{Context, RelocTarget};
use cranelift_reader::{ParseOptions, parse_test};
use target_lexicon::Triple;

/// A byte string: `len` bytes at `ptr`. Passed by value in both directions.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ZedClifBytes {
    /// The first byte; null only when `len` is 0.
    pub ptr: *const u8,
    /// The number of bytes.
    pub len: usize,
}

impl ZedClifBytes {
    /// The empty string, with a null pointer.
    const EMPTY: Self = Self {
        ptr: std::ptr::null(),
        len: 0,
    };

    /// The bytes of `s`, valid while `s` is.
    fn of(s: &[u8]) -> Self {
        Self {
            ptr: s.as_ptr(),
            len: s.len(),
        }
    }

    /// The bytes the caller passed, or an error naming `what` when the pointer is null and the
    /// length is not 0.
    ///
    /// # Safety
    ///
    /// When `ptr` is not null, `len` bytes from `ptr` are readable and unchanged for `'a`.
    unsafe fn read<'a>(self, what: &str) -> Result<&'a [u8], String> {
        if self.ptr.is_null() {
            return if self.len == 0 {
                Ok(&[])
            } else {
                Err(format!("{what}: a null pointer with length {}", self.len))
            };
        }
        // SAFETY: the caller's guarantee, above.
        Ok(unsafe { std::slice::from_raw_parts(self.ptr, self.len) })
    }

    /// The bytes the caller passed, as UTF-8 text.
    ///
    /// # Safety
    ///
    /// As [`Self::read`].
    unsafe fn text<'a>(self, what: &str) -> Result<&'a str, String> {
        // SAFETY: the caller's guarantee, passed on.
        let bytes = unsafe { self.read(what) }?;
        std::str::from_utf8(bytes).map_err(|e| format!("{what}: not UTF-8: {e}"))
    }
}

/// One relocation of a function's code, as [`zed_clif_image_relocation`] writes it.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ZedClifRelocation {
    /// The offset of the bytes to patch, from the start of the function's code.
    pub offset: u32,
    /// The value added to the symbol's address.
    pub addend: i64,
    /// Cranelift's name of the kind of relocation (`X86CallPCRel4`, `Abs8`, …).
    pub kind: ZedClifBytes,
    /// The symbol, named as in the crate documentation, "Names".
    pub symbol: ZedClifBytes,
}

/// A target handle: a target and its flags, from [`zed_clif_target_new`].
pub struct ZedClifTarget {
    isa: OwnedTargetIsa,
    /// The calling convention of a function whose signature names none: the target's own.
    call_conv: CallConv,
}

/// A code image: the functions of one CLIF text, compiled, from [`zed_clif_generate`].
pub struct ZedClifImage {
    functions: Vec<Compiled>,
}

/// One compiled function of an image.
struct Compiled {
    name: String,
    code: Vec<u8>,
    alignment: u32,
    relocations: Vec<Relocation>,
}

/// One relocation of a compiled function, its names owned.
struct Relocation {
    offset: u32,
    addend: i64,
    kind: String,
    symbol: String,
}

/// An error: its text, from any function that returns a handle or an image.
pub struct ZedClifError {
    text: String,
}

/// Runs `f`, catching a panic: its result, or the error it returned, or the panic's message.
fn guarded<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(result) => result,
        Err(payload) => {
            let message = payload
                .downcast_ref::<&str>()
                .map(|s| (*s).to_string())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "a panic with no message".to_string());
            Err(format!(
                "internal error in Cranelift or the shim: {message}"
            ))
        }
    }
}

/// Moves `value` to the heap for the caller, or, on an error, stores it in `*error` (when
/// `error` is not null) and returns null.
///
/// # Safety
///
/// `error` is null or writable.
unsafe fn give<T>(result: Result<T, String>, error: *mut *mut ZedClifError) -> *mut T {
    match result {
        Ok(value) => Box::into_raw(Box::new(value)),
        Err(text) => {
            if !error.is_null() {
                let e = Box::into_raw(Box::new(ZedClifError { text }));
                // SAFETY: `error` is writable, by the caller's guarantee.
                unsafe {
                    *error = e;
                }
            }
            std::ptr::null_mut()
        }
    }
}

/// Selects a target: `name` is a target triple (`x86_64-unknown-linux-gnu`,
/// `aarch64-apple-darwin`, …), or `host` for the machine the shim runs on, with the features its
/// processor has; `flags` is a list of settings separated by white space, each `name=value` or
/// a bare `name` for a boolean setting turned on, among Cranelift's shared settings
/// (`opt_level=speed`, `is_pic`, `enable_probestack`, …) and those of the target's instruction
/// set (`has_avx2`, …); a setting not given keeps Cranelift's default. Returns the target handle,
/// or null with `*error` set: a name that is not a triple, a target Cranelift does not support or
/// was built without, an unknown setting, a bad value.
///
/// # Safety
///
/// `name` and `flags` are readable as [`ZedClifBytes`] says; `error` is null or writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_target_new(
    name: ZedClifBytes,
    flags: ZedClifBytes,
    error: *mut *mut ZedClifError,
) -> *mut ZedClifTarget {
    let result = guarded(|| {
        // SAFETY: the caller's guarantee, passed on.
        let (name, flags) = unsafe { (name.text("the target")?, flags.text("the flags")?) };
        target(name, flags)
    });
    // SAFETY: the caller's guarantee, passed on.
    unsafe { give(result, error) }
}

/// The target `name` with the settings `flags` (see [`zed_clif_target_new`]).
fn target(name: &str, flags: &str) -> Result<ZedClifTarget, String> {
    let mut builder = if name == "host" {
        cranelift_native::builder().map_err(|e| format!("the host: {e}"))?
    } else {
        let triple = Triple::from_str(name).map_err(|e| format!("the target `{name}`: {e}"))?;
        isa::lookup(triple).map_err(|e| match e {
            LookupError::SupportDisabled => {
                format!("the target `{name}`: this build of Cranelift has no support for it")
            }
            LookupError::Unsupported => {
                format!("the target `{name}`: Cranelift does not support it")
            }
        })?
    };
    let mut shared = settings::builder();
    for item in flags.split_whitespace() {
        let (key, value) = match item.split_once('=') {
            Some((k, v)) => (k, Some(v)),
            None => (item, None),
        };
        let set = |c: &mut dyn Configurable| match value {
            Some(v) => c.set(key, v),
            None => c.enable(key),
        };
        // A shared setting first; a name it does not know may be the instruction set's.
        let outcome = match set(&mut shared) {
            Err(SetError::BadName(_)) => set(&mut builder),
            other => other,
        };
        outcome.map_err(|e| match e {
            SetError::BadName(_) => format!("the flag `{item}`: no setting `{key}`"),
            SetError::BadType => match value {
                Some(_) => format!("the flag `{item}`: `{key}` takes no value"),
                None => format!("the flag `{item}`: `{key}` needs a value, `{key}=<value>`"),
            },
            SetError::BadValue(why) => format!("the flag `{item}`: {why}"),
        })?;
    }
    let isa = builder
        .finish(settings::Flags::new(shared))
        .map_err(|e| format!("the target `{name}` with flags `{flags}`: {e}"))?;
    let call_conv = isa.default_call_conv();
    Ok(ZedClifTarget { isa, call_conv })
}

/// Releases a target handle; null is accepted and does nothing. An image generated with the
/// target stays valid.
///
/// # Safety
///
/// `target` is null or a handle from [`zed_clif_target_new`] not yet released; it is not used
/// again.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_target_free(target: *mut ZedClifTarget) {
    // A panic in a release (none is known in Cranelift's drops) is caught and dropped: a
    // release has no error to return.
    let _ = guarded(|| {
        if !target.is_null() {
            // SAFETY: the caller's guarantee: the box this crate made, released once.
            drop(unsafe { Box::from_raw(target) });
        }
        Ok(())
    });
}

/// Generates a code image: parses `clif`, Cranelift's text form of zero or more functions, and
/// verifies and compiles each function for `target`, in the order of the text. `symbols` points
/// to `symbol_count` names; the user name `u0:i` in the text is `symbols[i]`. Returns the image,
/// or null with `*error` set: text that is not UTF-8 or does not parse (the error names the
/// line), a function with no blocks, a function that fails Cranelift's verifier or that
/// Cranelift cannot compile or panics on (the error names the function, or, for a panic, holds
/// the panic's message), a user name with no symbol, a null target. The text may hold
/// functions only: a `test`, `target`, `set` or `feature` line is an error, since the target
/// and its settings come from the handle. A function whose signature names no calling
/// convention gets the target's.
///
/// # Safety
///
/// `target` is null or a live handle; `clif` and each of the `symbol_count` [`ZedClifBytes`] at
/// `symbols` (null when `symbol_count` is 0) are readable as [`ZedClifBytes`] says; `error` is
/// null or writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_generate(
    target: *const ZedClifTarget,
    clif: ZedClifBytes,
    symbols: *const ZedClifBytes,
    symbol_count: usize,
    error: *mut *mut ZedClifError,
) -> *mut ZedClifImage {
    let result = guarded(|| {
        if target.is_null() {
            return Err("no target: the target handle is null".to_string());
        }
        // SAFETY: the caller's guarantees: a live handle, readable bytes.
        let (target, text, names) = unsafe {
            let names = ZedClifBytes {
                ptr: symbols.cast(),
                len: symbol_count,
            };
            if names.ptr.is_null() && symbol_count != 0 {
                return Err(format!(
                    "the symbols: a null pointer with {symbol_count} symbols"
                ));
            }
            let list: &[ZedClifBytes] = if symbol_count == 0 {
                &[]
            } else {
                std::slice::from_raw_parts(symbols, symbol_count)
            };
            let mut names = Vec::with_capacity(list.len());
            for (i, s) in list.iter().enumerate() {
                names.push(s.text(&format!("symbol {i}"))?);
            }
            (&*target, clif.text("the CLIF text")?, names)
        };
        generate(target, text, &names)
    });
    // SAFETY: the caller's guarantee, passed on.
    unsafe { give(result, error) }
}

/// Parses `text` and compiles each of its functions for `target`, names resolved by `symbols`.
fn generate(target: &ZedClifTarget, text: &str, symbols: &[&str]) -> Result<ZedClifImage, String> {
    // Complexity tradeoff: one `Context` is cleared and reused for every function, so its
    // tables keep their capacity; a new `Context` per function (`Context::for_function`) would
    // allocate them again for each. Both are O(size of the text) for parsing plus, per function,
    // Cranelift's verifier and compiler on it, which this crate does not bound: their cost per
    // function is Cranelift's (not proved linear in the size of a function: register allocation
    // and the e-graph pass are Cranelift's own; the scaling test of `s07b_clif_shim_calls`
    // measures the number of functions at one size). Names are resolved per relocation by an
    // index into `symbols`, O(1) each, against O(symbols) for a search by name.
    if let Some((line, words)) = preamble_line(text) {
        return Err(format!(
            "the CLIF text, line {line}: `{words}` before the first function; the text may hold \
             functions only, since the target and its settings come from the handle"
        ));
    }
    let options = ParseOptions {
        default_calling_convention: target.call_conv,
        ..ParseOptions::default()
    };
    let file = parse_test(text, options).map_err(|e| format!("the CLIF text, line {e}"))?;
    let isa = &*target.isa;
    let libcall_names = cranelift_module::default_libcall_names();
    let mut ctx = Context::new();
    let mut functions = Vec::with_capacity(file.functions.len());
    for (func, _) in file.functions {
        ctx.clear();
        ctx.func = func;
        let name = function_name(&ctx.func, symbols)?;
        // Cranelift's verifier accepts a function with no blocks, and its compiler then panics
        // ("remove_constant_phis: entry block unknown", 0.137.1): an error here names the cause.
        if ctx.func.layout.entry_block().is_none() {
            return Err(format!("{name}: the function has no blocks"));
        }
        // `compile` runs the verifier itself when the setting `enable_verifier` is on (its
        // default); otherwise the function is verified here, so every function is verified once.
        if !isa.flags().enable_verifier() {
            ctx.verify(isa)
                .map_err(|e| format!("{name}: {}", pretty_verifier_error(&ctx.func, None, e)))?;
        }
        if let Err(e) = ctx.compile(isa, &mut ControlPlane::default()) {
            return Err(format!("{name}: {}", pretty_error(e.func, e.inner)));
        }
        // Read through `compiled_code`, a shared borrow, so the function's name table can be
        // read beside it; `compile`'s own result borrows the context mutably.
        let compiled = ctx
            .compiled_code()
            .expect("`compile` succeeded, so the context holds its compiled code");
        let buffer = &compiled.buffer;
        let code = buffer.data().to_vec();
        let alignment = buffer.min_alignment;
        let mut relocations = Vec::with_capacity(buffer.relocs().len());
        for r in buffer.relocs() {
            let symbol = match &r.target {
                RelocTarget::ExternalName(e) => {
                    external_name(e, &ctx.func, symbols, &libcall_names)?
                }
                RelocTarget::Label(_) => {
                    return Err(format!(
                        "{name}: a relocation at offset {} to a place inside the function, \
                         which the shim does not report",
                        r.offset
                    ));
                }
            };
            relocations.push(Relocation {
                offset: r.offset,
                addend: r.addend,
                kind: r.kind.to_string(),
                symbol,
            });
        }
        functions.push(Compiled {
            name,
            code,
            alignment,
            relocations,
        });
    }
    Ok(ZedClifImage { functions })
}

/// The first line of `text` before its first function that holds more than a comment, by its
/// number from 1, and its words: a `test`, `set`, `target` or `feature` line, which
/// `cranelift_reader::parse_test` reads there (any other word there it rejects itself). The
/// reader's own result cannot tell them all apart: it skips a `target` line for an instruction
/// set this build of Cranelift lacks, and its settings differ from the defaults with no `set`
/// line. A comment runs from `;` to the end of the line.
fn preamble_line(text: &str) -> Option<(usize, &str)> {
    for (i, line) in text.lines().enumerate() {
        let words = line.split(';').next().unwrap_or("").trim();
        if words.is_empty() {
            continue;
        }
        // The keyword, then a character that cannot continue a word (`function%f()` is valid).
        let keyword = words
            .strip_prefix("function")
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_'));
        if keyword {
            return None;
        }
        return Some((i + 1, words));
    }
    None
}

/// The symbol `u0:index`: `symbols[index]`, or an error.
fn user_symbol(namespace: u32, index: u32, symbols: &[&str]) -> Result<String, String> {
    if namespace != 0 {
        return Err(format!(
            "the name u{namespace}:{index}: only namespace 0 (`u0:<index>`) names symbols"
        ));
    }
    let i = usize::try_from(index).map_err(|e| format!("the name u0:{index}: {e}"))?;
    symbols
        .get(i)
        .map(|s| (*s).to_string())
        .ok_or_else(|| match symbols.len() {
            0 => format!("the name u0:{index}: no symbol names were given"),
            n => format!(
                "the name u0:{index}: there are {n} symbols, u0:0 to u0:{}",
                n - 1
            ),
        })
}

/// The name of function `func`, as the crate documentation, "Names", says.
fn function_name(func: &Function, symbols: &[&str]) -> Result<String, String> {
    match &func.name {
        UserFuncName::User(u) => user_symbol(u.namespace, u.index, symbols),
        UserFuncName::Testcase(t) => String::from_utf8(t.raw().to_vec())
            .map_err(|e| format!("a function name not UTF-8: {e}")),
    }
}

/// The name of the symbol `name` in function `func`, as the crate documentation, "Names", says.
fn external_name(
    name: &ExternalName,
    func: &Function,
    symbols: &[&str],
    libcall_names: &dyn Fn(cranelift_codegen::ir::LibCall) -> String,
) -> Result<String, String> {
    match name {
        ExternalName::User(r) => {
            let u = func
                .params
                .user_named_funcs()
                .get(*r)
                .ok_or_else(|| format!("the name {r}: not declared in the function"))?;
            user_symbol(u.namespace, u.index, symbols)
        }
        ExternalName::TestCase(t) => {
            String::from_utf8(t.raw().to_vec()).map_err(|e| format!("a name not UTF-8: {e}"))
        }
        ExternalName::LibCall(l) => Ok(libcall_names(*l)),
        ExternalName::KnownSymbol(k) => Ok(k.to_string()),
    }
}

/// Releases an image; null is accepted and does nothing.
///
/// # Safety
///
/// `image` is null or an image from [`zed_clif_generate`] not yet released; it is not used
/// again, nor any byte string read from it.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_free(image: *mut ZedClifImage) {
    let _ = guarded(|| {
        if !image.is_null() {
            // SAFETY: the caller's guarantee: the box this crate made, released once.
            drop(unsafe { Box::from_raw(image) });
        }
        Ok(())
    });
}

/// Function `index` of `image`, or `None` for a null image or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image, which outlives `'a`.
unsafe fn function<'a>(image: *const ZedClifImage, index: usize) -> Option<&'a Compiled> {
    // SAFETY: the caller's guarantee.
    let image = unsafe { image.as_ref() }?;
    image.functions.get(index)
}

/// The number of functions in `image`, in the order of the text; 0 for a null image.
///
/// # Safety
///
/// `image` is null or a live image.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_function_count(image: *const ZedClifImage) -> usize {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let image = unsafe { image.as_ref() };
        Ok(image.map_or(0, |i| i.functions.len()))
    })
    .unwrap_or(0)
}

/// The name of function `index` of `image` (the crate documentation, "Names"); the empty string
/// with a null pointer for a null image or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_name(
    image: *const ZedClifImage,
    index: usize,
) -> ZedClifBytes {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let f = unsafe { function(image, index) };
        Ok(f.map_or(ZedClifBytes::EMPTY, |f| ZedClifBytes::of(f.name.as_bytes())))
    })
    .unwrap_or(ZedClifBytes::EMPTY)
}

/// The machine code of function `index` of `image`, its constants and jump tables included (the
/// crate documentation, "Read-only data"); the empty string with a null pointer for a null image
/// or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_code(
    image: *const ZedClifImage,
    index: usize,
) -> ZedClifBytes {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let f = unsafe { function(image, index) };
        Ok(f.map_or(ZedClifBytes::EMPTY, |f| ZedClifBytes::of(&f.code)))
    })
    .unwrap_or(ZedClifBytes::EMPTY)
}

/// The alignment in bytes, a power of two, that the code of function `index` of `image` needs
/// where it is loaded; 0 for a null image or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_code_alignment(
    image: *const ZedClifImage,
    index: usize,
) -> u32 {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let f = unsafe { function(image, index) };
        Ok(f.map_or(0, |f| f.alignment))
    })
    .unwrap_or(0)
}

/// The number of relocations of function `index` of `image`, in the order of their offsets as
/// Cranelift gives them; 0 for a null image or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_relocation_count(
    image: *const ZedClifImage,
    index: usize,
) -> usize {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let f = unsafe { function(image, index) };
        Ok(f.map_or(0, |f| f.relocations.len()))
    })
    .unwrap_or(0)
}

/// Writes relocation `reloc` of function `index` of `image` to `*out` and returns true; returns
/// false and writes nothing for a null image or `out`, or an index past the last.
///
/// # Safety
///
/// `image` is null or a live image; `out` is null or writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_image_relocation(
    image: *const ZedClifImage,
    index: usize,
    reloc: usize,
    out: *mut ZedClifRelocation,
) -> bool {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let f = unsafe { function(image, index) };
        let Some(r) = f.and_then(|f| f.relocations.get(reloc)) else {
            return Ok(false);
        };
        if out.is_null() {
            return Ok(false);
        }
        let written = ZedClifRelocation {
            offset: r.offset,
            addend: r.addend,
            kind: ZedClifBytes::of(r.kind.as_bytes()),
            symbol: ZedClifBytes::of(r.symbol.as_bytes()),
        };
        // SAFETY: `out` is writable, by the caller's guarantee.
        unsafe {
            out.write(written);
        }
        Ok(true)
    })
    .unwrap_or(false)
}

/// The text of `error`, UTF-8; the empty string with a null pointer for a null error.
///
/// # Safety
///
/// `error` is null or an error from this crate not yet released.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_error_text(error: *const ZedClifError) -> ZedClifBytes {
    guarded(|| {
        // SAFETY: the caller's guarantee.
        let e = unsafe { error.as_ref() };
        Ok(e.map_or(ZedClifBytes::EMPTY, |e| ZedClifBytes::of(e.text.as_bytes())))
    })
    .unwrap_or(ZedClifBytes::EMPTY)
}

/// Releases an error; null is accepted and does nothing.
///
/// # Safety
///
/// `error` is null or an error from this crate not yet released; it is not used again, nor its
/// text.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn zed_clif_error_free(error: *mut ZedClifError) {
    let _ = guarded(|| {
        if !error.is_null() {
            // SAFETY: the caller's guarantee: the box this crate made, released once.
            drop(unsafe { Box::from_raw(error) });
        }
        Ok(())
    });
}

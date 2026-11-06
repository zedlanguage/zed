//! `zedc build <file> -o <out>` (step L1.36a): the program's code, compiled to an object file
//! as step L1.36 compiles it, linked with the runtime library into an executable that binds
//! its ports from its own command line as `zedc run` does.
//!
//! The runtime library is this crate built as a static library, `libzed_native.a`, which
//! Cargo writes beside the `zedc` executable; a library from another build of this crate is
//! refused, since the code `zedc` generates is joined to its own build's runtime only (see
//! [`runtime_of`]). The linker is the system's C compiler driver.
//! The link records no time, build path or random value, so two builds of one program give
//! the same bytes.

use std::any::TypeId;
use std::ffi::OsString;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use zedc::zir::lower::lower;

/// The system libraries the runtime library needs, as `rustc --print native-static-libs`
/// lists them for this crate on x86-64 Linux with glibc.
const SYSTEM_LIBS: &[&str] = &[
    "-lgcc_s",
    "-lutil",
    "-lrt",
    "-lpthread",
    "-lm",
    "-ldl",
    "-lc",
];

/// What a build links with: the C compiler driver that runs the linker, and the runtime
/// library.
#[derive(Clone, Debug)]
pub struct Toolchain {
    /// The linker's driver: `CC`, or `cc`.
    pub linker: OsString,
    /// The runtime library: `ZED_RUNTIME`, or `libzed_native.a` beside the running
    /// executable.
    pub runtime: PathBuf,
}

impl Toolchain {
    /// The toolchain the environment names, with the defaults above.
    pub fn from_env() -> Toolchain {
        let linker = std::env::var_os("CC").unwrap_or_else(|| "cc".into());
        let runtime = std::env::var_os("ZED_RUNTIME").map_or_else(
            || {
                std::env::current_exe()
                    .map(|exe| exe.with_file_name("libzed_native.a"))
                    .unwrap_or_else(|_| "libzed_native.a".into())
            },
            PathBuf::from,
        );
        Toolchain { linker, runtime }
    }
}

/// `zedc build <file> -o <out>`, with `args` the words after `build`. Returns the exit status:
/// 0; 1 when the program is rejected, does not compile or does not link; 2 for a usage
/// error, among them a missing linker or runtime library.
pub fn command(args: &[String], tools: &Toolchain, stderr: &mut dyn Write) -> u8 {
    let outcome = match args {
        [file, o, out] if o == "-o" => build(file, Path::new(out), tools, stderr),
        _ => Err((2, "usage: zedc build <file> -o <out>".to_string())),
    };
    match outcome {
        Ok(()) => 0,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

/// Builds the program in `file` into the executable `out` with `tools`, the program's
/// warnings written to `stderr`; on failure, the exit status and the message.
pub fn build(
    file: &str,
    out: &Path,
    tools: &Toolchain,
    stderr: &mut dyn Write,
) -> Result<(), (u8, String)> {
    if !tools.runtime.is_file() {
        return Err((
            2,
            format!(
                "the runtime library {} is missing: build it with `cargo build -p zed-native`, \
                 or name it in ZED_RUNTIME",
                tools.runtime.display()
            ),
        ));
    }
    // The object file is this executable's code generator's output, so the runtime library must
    // come from the same build of this crate; Cargo writes `libzed_native.a` beside `zedc`
    // only when it builds the library itself, so a later build of `zedc` alone (for a test,
    // or with other features) leaves an older library there.
    // The build is read from this executable's file, not from `BUILD` in memory, since only
    // its bytes in the file compare with the library's; reading `BUILD` here keeps the part of
    // this crate that holds it in every executable that can build.
    std::hint::black_box(&BUILD);
    let exe = std::env::current_exe().map_err(|e| (2, format!("this compiler's own path: {e}")))?;
    if !holds(&tools.runtime, &build_id(&exe).map_err(|e| (2, e))?).map_err(|e| (2, e))? {
        return Err((
            2,
            format!(
                "the runtime library {} is from another build of zed-native than {}: build \
                 both with `cargo build -p zed-native`, or name the matching one in ZED_RUNTIME",
                tools.runtime.display(),
                exe.display()
            ),
        ));
    }
    let program = zedc::run::load_file(file, stderr)?;
    let g = lower(&program.term()).map_err(|e| (1, format!("{file}: {e}")))?;
    let object = crate::executable_object(g, true, program.ports())
        .map_err(|e| (1, format!("{file}: {e}")))?;
    let mut at = out.as_os_str().to_owned();
    at.push(".zed.o");
    let at = PathBuf::from(at);
    // A file of the user's at that name is not overwritten.
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&at)
        .and_then(|mut f| f.write_all(&object))
        .map_err(|e| (1, format!("{}: {e}", at.display())))?;
    let linked = Command::new(&tools.linker)
        .arg("-o")
        .arg(out)
        .arg(&at)
        .arg(&tools.runtime)
        .args(SYSTEM_LIBS)
        // The runtime library holds the whole compiler; an executable needs a third of it.
        // Without this, a link took twice as long and wrote 41 MB in place of 14 MB.
        .arg("-Wl,--gc-sections")
        .output();
    let _ = std::fs::remove_file(&at);
    let linker = tools.linker.to_string_lossy();
    match linked {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Err((
            2,
            format!("the linker `{linker}` is missing: install a C compiler, or name one in CC"),
        )),
        Err(e) => Err((1, format!("the linker `{linker}`: {e}"))),
        Ok(o) if !o.status.success() => Err((
            1,
            format!(
                "the linker `{linker}` failed ({}):\n{}",
                o.status,
                String::from_utf8_lossy(&o.stderr).trim_end()
            ),
        )),
        Ok(_) => Ok(()),
    }
}

/// The runtime library in `dir` that was built with the executable `exe`: of the files
/// `libzed_native*.a` there, the first by name that holds `exe`'s [`BUILD`]. Cargo keeps one
/// such library for each set of features, dependencies and compiler flags it has built this
/// crate with, so the newest of them need not be `exe`'s.
pub fn runtime_of(exe: &Path, dir: &Path) -> Result<PathBuf, String> {
    let id = build_id(exe)?;
    let mut libraries = Vec::new();
    for entry in std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        if name.starts_with("libzed_native") && name.ends_with(".a") {
            libraries.push(path);
        }
    }
    libraries.sort_unstable();
    for library in libraries {
        if holds(&library, &id)? {
            return Ok(library);
        }
    }
    Err(format!(
        "no runtime library in {} was built with {}: build it with `cargo build -p zed-native`",
        dir.display(),
        exe.display()
    ))
}

/// The section of a file holding this crate that holds [`BUILD`].
pub const SECTION: &str = ".zed_native.build";

/// Which build of this crate a file holds: the runtime library, `zedc`, and any other
/// executable linked with this crate hold it as the bytes of [`SECTION`], which `strip` keeps,
/// unlike the symbol table. Two builds have equal bytes only if they agree in this crate's
/// hash and in the compiler's flags.
#[repr(C)]
pub struct Build {
    /// The identity of the type `Build`, which the compiler derives from this crate's hash:
    /// Cargo's hash of its features, its dependencies' builds, the profile, the target and
    /// the compiler.
    crate_hash: TypeId,
    /// A hash of the compiler's flags (`CARGO_ENCODED_RUSTFLAGS`), which the crate's hash
    /// leaves out; written by `build.rs`.
    rustflags: [u8; 8],
}

/// This build of the crate; see [`Build`].
#[used]
#[expect(
    unsafe_code,
    reason = "the build is read by its section's name from a stripped executable (NATIVE-build-id)"
)]
#[unsafe(link_section = ".zed_native.build")]
pub static BUILD: Build = Build {
    crate_hash: const { TypeId::of::<Build>() },
    rustflags: include!(concat!(env!("OUT_DIR"), "/rustflags.rs")),
};

/// The bytes of [`SECTION`] in the executable or object file `exe`: the [`BUILD`] of the
/// zed-native it holds.
pub fn build_id(exe: &Path) -> Result<Vec<u8>, String> {
    let file = std::fs::File::open(exe).map_err(|e| format!("{}: {e}", exe.display()))?;
    let cache = object::ReadCache::new(file);
    section(&cache, exe)?.ok_or_else(|| {
        format!(
            "{} has no section {SECTION}, which names the build of zed-native it holds, so \
             the runtime library built with it cannot be found: it does not hold zed-native",
            exe.display()
        )
    })
}

/// The bytes of [`SECTION`] in the object file or executable `data` read from `file`, if it
/// has that section.
fn section<'a, R: object::ReadRef<'a>>(data: R, file: &Path) -> Result<Option<Vec<u8>>, String> {
    use object::{Object as _, ObjectSection as _};
    let at = |e: &dyn std::fmt::Display| format!("{}: {e}", file.display());
    let object = object::File::parse(data).map_err(|e| at(&e))?;
    object
        .section_by_name(SECTION)
        .map(|s| s.data().map(<[u8]>::to_vec).map_err(|e| at(&e)))
        .transpose()
}

/// Whether the archive `library` holds the build `id`: whether a member that its symbol index
/// names as defining [`BUILD`] has `id` in its [`SECTION`]. [`BUILD`]'s mangled name, in either
/// of Rust's manglings, is `_RNvNtCs<hash>_10zed_native4link5BUILD` or
/// `_ZN10zed_native4link5BUILD17h<hash>E`.
fn holds(library: &Path, id: &[u8]) -> Result<bool, String> {
    let at = |e: &dyn std::fmt::Display| format!("{}: {e}", library.display());
    let file = std::fs::File::open(library).map_err(|e| at(&e))?;
    let cache = object::ReadCache::new(file);
    let archive = object::read::archive::ArchiveFile::parse(&cache).map_err(|e| at(&e))?;
    let Some(symbols) = archive.symbols().map_err(|e| at(&e))? else {
        return Ok(false);
    };
    for s in symbols {
        let s = s.map_err(|e| at(&e))?;
        let name = s.name();
        if (name.starts_with(b"_RNvNtCs") && name.ends_with(b"_10zed_native4link5BUILD"))
            || name.starts_with(b"_ZN10zed_native4link5BUILD17h")
        {
            let (offset, size) = archive.member(s.offset()).map_err(|e| at(&e))?.file_range();
            if section(cache.range(offset, size), library)?.as_deref() == Some(id) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

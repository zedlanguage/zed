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
//!
//! The executable records the key of its link, the hash of everything that entered it, as its
//! GNU build ID (step L1.36b, see [`Identity`]); a build whose output already records the key
//! it would link with leaves that output as it is.

use std::any::TypeId;
use std::ffi::OsString;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use zedc::suppress::Suppress;
use zedc::work::{self, Stage};
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

/// The flags of every link, after the system libraries. The runtime library holds the whole
/// compiler; an executable needs a third of it. Without `--gc-sections`, a link took twice as
/// long and wrote 41 MB in place of 14 MB.
const LINK_FLAGS: &[&str] = &["-Wl,--gc-sections"];

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

/// `zedc build <file> -o <out> [--suppress <address> …]`, with `args` the words after
/// `build`; a warning whose address is named is not printed (DESIGN.md sec:diagnostics).
/// Returns the exit status: 0; 1 when the program is rejected, does not compile or does not
/// link; 2 for a usage error, among them a missing linker or runtime library.
pub fn command(args: &[String], tools: &Toolchain, stderr: &mut dyn Write) -> u8 {
    let words: Vec<&str> = args.iter().map(String::as_str).collect();
    let outcome = Suppress::take(&words).map_err(|why| (2, why)).and_then(
        |(mut suppress, rest)| match rest[..] {
            [file, "-o", out] => build(file, Path::new(out), &mut suppress, tools, stderr),
            _ => Err((
                2,
                "usage: zedc build <file> -o <out> [--suppress <address> …]".to_string(),
            )),
        },
    );
    match outcome {
        Ok(()) => 0,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

/// Builds the program in `file` into the executable `out` with `tools`, the program's
/// warnings that `suppress` does not name written to `stderr`; on failure, the exit status
/// and the message.
pub fn build(
    file: &str,
    out: &Path,
    suppress: &mut Suppress,
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
    let program = zedc::run::load_file(file, suppress, stderr)?;
    let g = work::stage(Stage::Lower, None, || lower(&program.term()))
        .map_err(|e| (1, format!("{file}: {e}")))?;
    let address = program.address().map_err(|e| (1, format!("{file}: {e}")))?;
    let object = work::stage(Stage::Codegen, None, || {
        crate::executable_object(g, true, program.ports(), address)
    })
    .map_err(|e| (1, format!("{file}: {e}")))?;
    let key = Identity::of(tools)?.key(&object);
    if recorded(out).as_deref() == Some(key.as_bytes()) {
        work::cached(Stage::Link, None);
        return Ok(());
    }
    sweep(out);
    let scratch = Scratch::new(out)?;
    let (at, linked_at) = (
        scratch.path.join("program.o"),
        scratch.path.join(&scratch.name),
    );
    std::fs::write(&at, &object).map_err(|e| (1, format!("{}: {e}", at.display())))?;
    let linked = work::stage(Stage::Link, None, || {
        Command::new(&tools.linker)
            .arg("-o")
            .arg(&linked_at)
            .arg(&at)
            .arg(&tools.runtime)
            .args(SYSTEM_LIBS)
            .args(LINK_FLAGS)
            .arg(format!("-Wl,--build-id=0x{}", key.to_hex()))
            .output()
    });
    let linker = tools.linker.to_string_lossy();
    match linked {
        Err(e) => Err(not_run(&linker, &e)),
        Ok(o) if !o.status.success() => Err((
            1,
            format!(
                "the linker `{linker}` failed ({}):\n{}",
                o.status,
                String::from_utf8_lossy(&o.stderr).trim_end()
            ),
        )),
        // In one step, so that a build reading `out` at the same time, for its key or to run
        // it, reads the executable before or the one after, never one half written.
        Ok(_) => {
            std::fs::rename(&linked_at, out).map_err(|e| (1, format!("{}: {e}", out.display())))
        }
    }
}

/// The directory a build of `out` writes its object file and links in:
/// `<out>.zed-build.<pid>.<k>`, beside `out`, with `<pid>` the process's id and `<k>` the
/// number of the attempt in this process. A name of its own for each build, so a directory
/// left by a build stopped by a signal (SIGKILL, or SIGINT, which unwinds nothing) blocks no
/// later build, and builds of one output at the same time do not meet; beside `out`, so the
/// executable is moved to `out` by a rename. The build holds the directory locked (`flock`)
/// while it lives, which the kernel releases when the process ends however it ends: a
/// directory of this name that is not locked is a stopped build's, and [`sweep`] removes it.
/// Dropping a `Scratch`, on success, on error and in unwinding from a panic, removes it.
struct Scratch {
    /// The directory.
    path: PathBuf,
    /// The name of `out` in its directory, which the linker's output takes in this one.
    name: OsString,
    /// The directory, open and locked.
    _lock: std::fs::File,
}

/// The number of the next attempt at a working directory in this process.
static ATTEMPT: AtomicU64 = AtomicU64::new(0);

impl Scratch {
    /// A new working directory for a build of `out`, created and locked. A name taken already
    /// is passed over for the next attempt's. A directory that [`sweep`] in another build
    /// removed between its creation and its lock, which that build took for a stopped
    /// build's, is passed over the same way: after its lock is taken, the name must still
    /// name it.
    fn new(out: &Path) -> Result<Scratch, (u8, String)> {
        let name = out.file_name().ok_or_else(|| {
            (
                2,
                format!(
                    "the output {} names a directory, not a file: name the executable to build",
                    out.display()
                ),
            )
        })?;
        loop {
            let mut path = out.as_os_str().to_owned();
            path.push(format!(
                ".zed-build.{}.{}",
                std::process::id(),
                ATTEMPT.fetch_add(1, Ordering::Relaxed)
            ));
            let path = PathBuf::from(path);
            let failed = |e: std::io::Error| (1, format!("{}: {e}", path.display()));
            match std::fs::create_dir(&path) {
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                made => made.map_err(failed)?,
            }
            let lock = match std::fs::File::open(&path) {
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                opened => opened.map_err(failed)?,
            };
            lock.lock().map_err(failed)?;
            if names(&path, &lock) {
                return Ok(Scratch {
                    path,
                    name: name.to_owned(),
                    _lock: lock,
                });
            }
        }
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        // Best effort, while the lock is held: the lock is released after, when the field
        // `_lock` is dropped.
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Whether `path` names the open file `file`, not another or none.
fn names(path: &Path, file: &std::fs::File) -> bool {
    use std::os::unix::fs::MetadataExt as _;
    match (std::fs::symlink_metadata(path), file.metadata()) {
        (Ok(a), Ok(b)) => (a.dev(), a.ino()) == (b.dev(), b.ino()),
        _ => false,
    }
}

/// Removes the working directories that builds of `out` stopped by a signal left beside it
/// (see [`Scratch`]): each directory in `out`'s directory named `<out>.zed-build.<n>.<n>`,
/// with `<n>` digits, whose lock this process can take. A running build holds its own locked,
/// so it is kept. One read of the directory, and one open and lock of each such name: linear
/// in the directory's entries. Best effort: a directory that cannot be read, opened or
/// removed is left, and the build goes on, since what is left blocks no build.
pub fn sweep(out: &Path) {
    let Some(name) = out.file_name() else {
        return;
    };
    let dir = match out.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let mut prefix = name.to_owned();
    prefix.push(".zed-build.");
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let digits =
        |p: Option<&[u8]>| p.is_some_and(|p| !p.is_empty() && p.iter().all(u8::is_ascii_digit));
    for entry in entries.flatten() {
        let entry_name = entry.file_name();
        let Some(rest) = entry_name
            .as_encoded_bytes()
            .strip_prefix(prefix.as_encoded_bytes())
        else {
            continue;
        };
        let mut parts = rest.split(|&b| b == b'.');
        if !(digits(parts.next()) && digits(parts.next()) && parts.next().is_none())
            || !entry.file_type().is_ok_and(|t| t.is_dir())
        {
            continue;
        }
        let path = entry.path();
        let Ok(lock) = std::fs::File::open(&path) else {
            continue;
        };
        // After the lock, the name must still name the directory locked: a build may have
        // made a new one of that name since this one was opened.
        if lock.try_lock().is_ok() && names(&path, &lock) {
            let _ = std::fs::remove_dir_all(&path);
        }
    }
}

/// The error of a linker that could not be run: status 2 if it is missing, else status 1.
fn not_run(linker: &str, e: &std::io::Error) -> (u8, String) {
    if e.kind() == std::io::ErrorKind::NotFound {
        (
            2,
            format!("the linker `{linker}` is missing: install a C compiler, or name one in CC"),
        )
    } else {
        (1, format!("the linker `{linker}`: {e}"))
    }
}

/// What a link reads besides its object file (step L1.36b), each named by its content, not
/// by its path, so that a toolchain copied or reached by another path has the same identity
/// and a changed one has another.
///
/// - The linker is named by what its driver writes to standard output for `--version` and
///   for `-Wl,--version`: the driver's version and, through it, the linker's. Two spawns
///   that do no work, under 5 ms together; hashing the driver's file would miss the linker,
///   the C runtime start files and `libgcc`, which the driver finds by itself.
/// - The runtime library is named by the BLAKE3 hash of its bytes: about 0.1 s for its
///   117 MB, once per build. Its [`BUILD`] is not enough, since it names the crate's Cargo
///   configuration and not its source.
///
/// Not named: the system libraries in [`SYSTEM_LIBS`] and the start files, which a system
/// update can change under one driver version, and the driver's environment variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identity {
    /// The driver's standard output for `--version` and for `-Wl,--version`.
    pub linker: [Vec<u8>; 2],
    /// The BLAKE3 hash of the runtime library's bytes.
    pub runtime: blake3::Hash,
}

impl Identity {
    /// The identity of `tools`. A linker that cannot be run, fails to give its version or
    /// gives an empty one is an error, since links by two such linkers could not be told
    /// apart.
    pub fn of(tools: &Toolchain) -> Result<Identity, (u8, String)> {
        let linker = tools.linker.to_string_lossy();
        let version = |arg: &str| {
            let o = Command::new(&tools.linker)
                .arg(arg)
                .output()
                .map_err(|e| not_run(&linker, &e))?;
            if !o.status.success() {
                return Err((
                    1,
                    format!(
                        "the linker `{linker}` gave no version: `{linker} {arg}` failed ({}):\n{}",
                        o.status,
                        String::from_utf8_lossy(&o.stderr).trim_end()
                    ),
                ));
            }
            if o.stdout.is_empty() {
                return Err((
                    1,
                    format!(
                        "the linker `{linker}` wrote nothing for `{linker} {arg}`, so its links \
                         cannot be told from another linker's: name a C compiler that gives \
                         its version in CC"
                    ),
                ));
            }
            Ok(o.stdout)
        };
        let linker = [version("--version")?, version("-Wl,--version")?];
        let at = |e: std::io::Error| (1, format!("{}: {e}", tools.runtime.display()));
        let mut runtime = blake3::Hasher::new();
        runtime
            .update_reader(std::fs::File::open(&tools.runtime).map_err(at)?)
            .map_err(at)?;
        Ok(Identity {
            linker,
            runtime: runtime.finalize(),
        })
    }

    /// The key of the link of `object` with the toolchain of this identity: a BLAKE3 hash of
    /// everything that enters the executable, which is the object file, this identity and the
    /// link's arguments other than the paths, each preceded by its length. The link records
    /// it as the executable's GNU build ID, so that equal executables come from equal inputs,
    /// and a build whose output already records its key does not link again. Equal keys are
    /// taken for equal inputs with no comparison of the inputs, so the cache rests on
    /// BLAKE3's collision resistance (DESIGN.md sec:theories, the trusted base).
    pub fn key(&self, object: &[u8]) -> blake3::Hash {
        let mut key = blake3::Hasher::new_derive_key("zed-native 2026-11-07 the key of a link");
        let mut part = |bytes: &[u8]| {
            key.update(&bytes.len().to_le_bytes());
            key.update(bytes);
        };
        part(object);
        part(self.runtime.as_bytes());
        for v in &self.linker {
            part(v);
        }
        for a in SYSTEM_LIBS.iter().chain(LINK_FLAGS) {
            part(a.as_bytes());
        }
        key.finalize()
    }
}

/// The key the link that wrote the executable `out` recorded: its GNU build ID. `None` if
/// `out` cannot be read, is not an object file or has no build ID, each of which the link
/// that follows replaces or reports.
pub fn recorded(out: &Path) -> Option<Vec<u8>> {
    use object::Object as _;
    let cache = object::ReadCache::new(std::fs::File::open(out).ok()?);
    let file = object::File::parse(&cache).ok()?;
    file.build_id().ok().flatten().map(<[u8]>::to_vec)
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

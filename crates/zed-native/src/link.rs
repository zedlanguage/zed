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
//! it would link with, and still has the bytes its link wrote, leaves that output as it is
//! (LINK-key-deps, see [`Record`]).

use std::any::TypeId;
use std::ffi::OsString;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use zedc::suppress::Suppress;
use zedc::work::{self, Stage};
use zedc::zir::lower::lower_sited;

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

/// The flags of the link that makes the prelinked runtime ([`prelinked`]) from the runtime
/// library, before `-Wl,-u,<symbol>` for each symbol of [`roots`]: a relocatable link (`-r`)
/// that keeps only the sections those symbols reach (`--gc-sections`), with no C start files
/// or system libraries (`-nostdlib`), which the link of each program adds.
const PRELINK_FLAGS: &[&str] = &["-r", "-nostdlib", "-Wl,--gc-sections"];

/// The symbols of the runtime library that a program's object file can name: each runtime
/// hook ([`crate::hooks::HOOKS`]) and `zed_main`, which the program's `main` calls
/// ([`crate::exe`]). The prelinked runtime keeps what they reach.
fn roots() -> impl Iterator<Item = &'static str> {
    crate::hooks::HOOKS
        .iter()
        .map(|&(name, _, _)| name)
        .chain(["zed_main"])
}

/// The environment variables that the C compiler driver or its linker reads and that can change
/// which files a link reads or what it writes: GCC's `GCC_EXEC_PREFIX`, `COMPILER_PATH` and
/// `LIBRARY_PATH` (Clang reads the last two too), and the linker's `LD_RUN_PATH`,
/// `LD_LIBRARY_PATH` (where GNU ld looks for the libraries a shared library needs),
/// `LDEMULATION` (GNU ld's default emulation) and `GNUTARGET` (GNU ld's default input object
/// format). Not in the key: `/etc/ld.so.conf` and the files it includes, which GNU ld reads
/// only for a library a shared library needs that it found in no directory before them (a
/// `zedc build` link read none, traced 2026-11-07); the library found that way is listed and
/// hashed, and a change to them alone is a change of search path, the limit `kept` names.
/// Not named: `PATH`, through which the driver may find its linker, since the linker's version
/// enters the key in its place, and variables that change only the language of messages or
/// where scratch files go.
pub const DRIVER_ENV: &[&str] = &[
    "GCC_EXEC_PREFIX",
    "COMPILER_PATH",
    "LIBRARY_PATH",
    "LD_RUN_PATH",
    "LD_LIBRARY_PATH",
    "LDEMULATION",
    "GNUTARGET",
];

/// The values of [`DRIVER_ENV`] in this process's environment, in that order; `None` for one
/// that is not set.
pub fn driver_env() -> Vec<(&'static str, Option<OsString>)> {
    DRIVER_ENV
        .iter()
        .map(|&name| (name, std::env::var_os(name)))
        .collect()
}

/// What a build links with: the C compiler driver that runs the linker, the runtime
/// library, and the driver's environment.
#[derive(Clone, Debug)]
pub struct Toolchain {
    /// The linker's driver: `CC`, or `cc`.
    pub linker: OsString,
    /// The runtime library: `ZED_RUNTIME`, or `libzed_native.a` beside the running
    /// executable.
    pub runtime: PathBuf,
    /// The variables of [`DRIVER_ENV`] the driver runs with, `None` for one removed from its
    /// environment, as [`driver_env`] gives them: every run of the driver has exactly these,
    /// so the key of a link names the environment the link had.
    pub env: Vec<(&'static str, Option<OsString>)>,
}

impl Toolchain {
    /// A command that runs the driver, with [`Toolchain::env`] set in its environment.
    fn driver(&self) -> Command {
        let mut command = Command::new(&self.linker);
        for (name, value) in &self.env {
            match value {
                Some(value) => command.env(name, value),
                None => command.env_remove(name),
            };
        }
        command
    }

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
        Toolchain {
            linker,
            runtime,
            env: driver_env(),
        }
    }
}

/// The message of a `zedc build` command line that is not one.
pub const USAGE: &str = "zedc build takes the program's file and, after `-o`, the executable to \
                         write: `zedc build <file> -o <out> [--suppress <address> …] [--addresses] \
                         [--option <name> …]`, as in \
                         `zedc build hello.zed -o hello`";

/// `zedc build <file> -o <out> [--suppress <address> …] [--addresses] [--option <name> …]`,
/// with `args` the words after `build`; a warning whose address is named is not printed
/// (DESIGN.md sec:diagnostics), and each option named is turned on (step L2.8d).
/// Returns the exit status: 0; 1 when the program is rejected, does not compile or does not
/// link; 2 for a usage error, among them a missing linker or runtime library.
pub fn command(args: &[String], tools: &Toolchain, stderr: &mut dyn Write) -> u8 {
    let words: Vec<&str> = args.iter().map(String::as_str).collect();
    let outcome = Suppress::take(&words)
        .and_then(|(suppress, rest)| Ok((suppress, zedc::build::take(&rest)?)))
        .map_err(|why| (2, why))
        .and_then(|(mut suppress, (on, rest))| match rest[..] {
            [file, "-o", out] => build(file, Path::new(out), &on, &mut suppress, tools, stderr),
            _ => Err((2, USAGE.to_string())),
        });
    match outcome {
        Ok(()) => 0,
        Err((status, why)) => {
            let _ = writeln!(stderr, "{why}");
            status
        }
    }
}

/// Builds the program in `file`, with the options `on` turned on, into the executable `out`
/// with `tools`, the program's warnings that `suppress` does not name written to `stderr`; on
/// failure, the exit status and the message.
pub fn build(
    file: &str,
    out: &Path,
    on: &[&str],
    suppress: &mut Suppress,
    tools: &Toolchain,
    stderr: &mut dyn Write,
) -> Result<(), (u8, String)> {
    if !tools.runtime.is_file() {
        return Err((
            2,
            format!(
                "zedc cannot build an executable: the runtime library {}, which every executable \
                 is linked with, is missing. Repairs: build it with `cargo build -p zed-native`, \
                 which writes it beside zedc, or name its path in the environment variable \
                 ZED_RUNTIME",
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
    let exe = std::env::current_exe().map_err(|e| {
        (
            2,
            format!(
                "zedc cannot build an executable: it could not find its own file, which it reads \
                 to check that the runtime library was built with it ({e}). Repair: run zedc by \
                 its path"
            ),
        )
    })?;
    let unchecked = |e: String| {
        (
            2,
            format!(
                "zedc cannot build an executable: it could not check that the runtime library {} \
                 was built with it: {e}",
                tools.runtime.display()
            ),
        )
    };
    if !holds(&tools.runtime, &build_id(&exe).map_err(unchecked)?).map_err(unchecked)? {
        return Err((
            2,
            format!(
                "zedc cannot build an executable: the runtime library {} comes from another build \
                 of zed-native than this zedc, {}, and code one build makes does not run with \
                 another's library. Repairs: build both again with `cargo build -p zed-native`, \
                 or name the library built with this zedc in ZED_RUNTIME",
                tools.runtime.display(),
                exe.display()
            ),
        ));
    }
    let program = zedc::run::load_file(file, on, suppress, stderr)?;
    let (g, sites) = work::stage(Stage::Lower, None, || {
        lower_sited(&program.term(), Some(program.sites()))
    })
    .map_err(|e| (1, format!("{file}: {e}")))?;
    let address = program.address().map_err(|e| (1, format!("{file}: {e}")))?;
    let object = work::stage(Stage::Codegen, None, || {
        crate::executable_object(
            g,
            true,
            program.ports(),
            &program.limits(),
            address,
            (program.file(), program.text()),
            &sites,
        )
    })
    .map_err(|e| (1, format!("{file}: {e}")))?;
    let identity = Identity::of(tools)?;
    if kept(out, &identity, &object, tools) {
        work::cached(Stage::Link, None);
        return Ok(());
    }
    sweep(out);
    let runtime = prelinked(tools, &identity, out)?;
    let scratch = Scratch::new(out)?;
    // The linker's output takes `out`'s name, and the files beside it that name with a suffix,
    // so no output name meets another file here.
    let named = |suffix: &str| {
        let mut name = scratch.name.clone();
        name.push(suffix);
        scratch.path.join(name)
    };
    let (at, linked_at, listed_at, record_at) = (
        named(".o"),
        scratch.path.join(&scratch.name),
        named(".d"),
        named(".zed-link"),
    );
    std::fs::write(&at, &object).map_err(|e| unwritable(&at, &e, out))?;
    // The files the link reads are known only once it has read them, so the link writes the
    // key without them in its build ID, and the key with them replaces it after.
    let partial = identity.key(&object, &[]);
    let mut list = OsString::from("--dependency-file=");
    list.push(&listed_at);
    let linked = work::stage(Stage::Link, None, || {
        tools
            .driver()
            .arg("-o")
            .arg(&linked_at)
            .arg(&at)
            .arg(&runtime.path)
            .args(SYSTEM_LIBS)
            .args(LINK_FLAGS)
            .arg(format!("-Wl,--build-id=0x{}", partial.to_hex()))
            // `-Xlinker`, not `-Wl,`, which would split a path at its commas.
            .arg("-Xlinker")
            .arg(list)
            .output()
    });
    let linker = tools.linker.to_string_lossy();
    match linked {
        Err(e) => return Err(not_run(&linker, &e)),
        Ok(o) if !o.status.success() => {
            return Err((
                1,
                format!(
                    "zedc could not link {}: the linker `{linker}` failed ({}). Repair: check \
                     that `{linker}` links C programs, or name another C compiler in the \
                     environment variable CC. The linker printed:\n{}",
                    out.display(),
                    o.status,
                    String::from_utf8_lossy(&o.stderr).trim_end()
                ),
            ));
        }
        Ok(_) => {}
    }
    let listed = std::fs::read(&listed_at).map_err(|e| {
        (
            1,
            format!(
                "zedc could not finish {}: the linker `{linker}` wrote no list of the files it \
                 read ({e}), and zedc needs that list to tell when the executable must be linked \
                 again. Repair: name in CC a C compiler whose linker takes --dependency-file, as \
                 GNU ld 2.35 and later and LLD do",
                out.display()
            ),
        )
    })?;
    // The prelinked runtime is made from the runtime library alone by a link that the key
    // names in full ([`Identity::key`]), so it is skipped as the library is.
    let inputs = Inputs::of(dependencies(&listed), &[&at, &tools.runtime, &runtime.path]).map_err(|e| {
        (
            1,
            format!(
                "zedc could not finish {}: the linker `{linker}` read a file that cannot be read \
                 now ({e}), and zedc reads every file a link read to tell when the executable \
                 must be linked again. Repair: build again, after putting back the file if it \
                 was moved or removed",
                out.display()
            ),
        )
    })?;
    let key = identity.key(&object, &inputs.hashes);
    let unfinished = |e: String| (1, format!("zedc could not finish {}: {e}", out.display()));
    if !write_build_id(&linked_at, &partial, &key).map_err(unfinished)? {
        return Err((
            1,
            format!(
                "zedc could not finish {}: the linker `{linker}` wrote it without the build ID \
                 zedc gave it, where zedc records which files the executable was linked from. \
                 Repair: name in CC a C compiler whose linker takes --build-id",
                out.display()
            ),
        ));
    }
    let record = Record {
        output: hash_file(&linked_at).map_err(unfinished)?,
        inputs: inputs.paths,
    };
    std::fs::write(&record_at, record.to_bytes()).map_err(|e| unwritable(&record_at, &e, out))?;
    // Each in one step, so that a build reading `out` at the same time, for its key or to run
    // it, reads the executable before or the one after, never one half written. The record
    // follows the executable: a build that finds one with the other's predecessor, after a
    // build stopped between the two, or two builds of `out` at once, finds that the
    // executable's bytes are not the record's, and links again.
    let rename =
        |from: &Path, to: &Path| std::fs::rename(from, to).map_err(|e| unwritable(to, &e, out));
    rename(&linked_at, out)?;
    rename(&record_at, &Record::path(out))
}

/// The runtime library prelinked (PERF-link-archive): one relocatable object file holding only
/// the sections of the library that [`roots`] reach, made by the driver with [`PRELINK_FLAGS`]
/// once for each [`Identity::prelink_key`] and kept, which each link takes in place of the
/// library.
///
/// It is kept beside the library as `<library>.<hash of the library>.<key>.o`, both in
/// hexadecimal; when that directory cannot be written, as for an installed library, beside
/// `out`. Each toolchain that links with one library has an object of its own there, made
/// once. The build that makes one holds the lock file `<library>.prelink.lock` of that
/// directory, so one build at a time makes one; it writes the object under another name and
/// renames it, so a build that reads the object, which takes no lock, reads all of it or finds
/// none. The maker then removes the objects made from other bytes of the library, which Cargo
/// replaced since, and the unfinished files of makers that were stopped, which no maker writes
/// while it holds the lock. A build still running with the library it replaced, which finds its
/// object removed before its linker opens it, fails, and the next build links again.
//
// Complexity tradeoff: the library is the whole compiler (227 MB). A link of the library
// itself reads its symbol index, loads every member a program reaches and drops the unreached
// sections again: about 4.0 billion instructions and 1.3 to 3.7 s with GNU ld 2.46 (measured
// 2026-11-15, load 75 to 95). That work depends on the runtime and the linker alone, so it is
// done once and kept: the prelinked object (49 MB) links in about 1.0 billion instructions and
// 1.3 to 1.7 s (a whole build of l01_21's fahrenheit.zed, 1.05 to 1.83 s at load 61), a
// 3.8-fold cut in the link's work, keeping the same sections but for a few
// `Debug` functions. The first build after the runtime changes pays about 4.2 s more, once.
// LLD links the library in 0.9 billion instructions and the prelinked object in 0.4 billion,
// but would be a new dependency of every build, which is the author's decision.
struct Prelinked {
    /// The prelinked object.
    path: PathBuf,
}

/// The prelinked runtime of `tools` for the build of `out`, made if it is not there; see
/// [`Prelinked`].
fn prelinked(
    tools: &Toolchain,
    identity: &Identity,
    out: &Path,
) -> Result<Prelinked, (u8, String)> {
    let dir_of = |p: &Path| match p.parent() {
        Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
        _ => PathBuf::from("."),
    };
    let library = tools.runtime.file_name().unwrap_or_default().to_owned();
    let mut lock_name = library.clone();
    lock_name.push(".prelink.lock");
    let mut name = library.clone();
    name.push(format!(
        ".{}.{}.o",
        identity.runtime.to_hex(),
        identity.prelink_key().to_hex()
    ));
    let mut refused = None;
    for dir in [dir_of(&tools.runtime), dir_of(out)] {
        let path = dir.join(&name);
        if path.is_file() {
            return Ok(Prelinked { path });
        }
        let lock_path = dir.join(&lock_name);
        let lock = match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&lock_path)
        {
            Ok(lock) => lock,
            Err(e) => {
                refused = Some(unwritable(&lock_path, &e, out));
                continue;
            }
        };
        // Released when `lock` is dropped, on every path out.
        lock.lock().map_err(|e| unwritable(&lock_path, &e, out))?;
        if path.is_file() {
            return Ok(Prelinked { path });
        }
        match prelink(tools, identity, &dir, &library, &path, out)? {
            Ok(()) => return Ok(Prelinked { path }),
            Err(e) => refused = Some(e),
        }
    }
    Err(refused.unwrap_or_else(|| (1, format!("zedc could not build {}", out.display()))))
}

/// Makes the prelinked object `path` in `dir` from the runtime library of `tools`, whose file
/// name is `library` and whose hash is in `identity`, with the lock of `dir` held; then removes
/// the prelinked objects in `dir` made from other bytes of that library, and the unfinished
/// files of stopped makers. One read of the directory: linear in its entries. `Ok(Err(why))`
/// if no file can be made in `dir`, as when its permissions or a read-only file system refuse
/// it, which the lock file, made before, need not show.
fn prelink(
    tools: &Toolchain,
    identity: &Identity,
    dir: &Path,
    library: &std::ffi::OsStr,
    path: &Path,
    out: &Path,
) -> Result<Result<(), (u8, String)>, (u8, String)> {
    let mut unfinished = path.as_os_str().to_owned();
    unfinished.push(format!(".{}", std::process::id()));
    let unfinished = PathBuf::from(unfinished);
    if let Err(e) = std::fs::File::create(&unfinished) {
        return Ok(Err(unwritable(&unfinished, &e, out)));
    }
    // Not a stage of the build's report: it is made for many builds, by the first that needs
    // it, and the report's link row counts this build's link alone.
    let made = tools
        .driver()
        .args(PRELINK_FLAGS)
        .args(roots().map(|r| format!("-Wl,-u,{r}")))
        .arg(&tools.runtime)
        .arg("-o")
        .arg(&unfinished)
        .output();
    let linker = tools.linker.to_string_lossy();
    match made {
        Err(e) => return Err(not_run(&linker, &e)),
        Ok(o) if !o.status.success() => {
            let _ = std::fs::remove_file(&unfinished);
            return Err((
                1,
                format!(
                    "zedc could not prelink the runtime library {} for {}: the linker \
                     `{linker}` failed ({}). Repair: check that `{linker}` links C programs and \
                     takes -r, or name another C compiler in the environment variable CC. The \
                     linker printed:\n{}",
                    tools.runtime.display(),
                    out.display(),
                    o.status,
                    String::from_utf8_lossy(&o.stderr).trim_end()
                ),
            ));
        }
        Ok(_) => {}
    }
    std::fs::rename(&unfinished, path).map_err(|e| unwritable(path, &e, out))?;
    // Best effort: what is left takes room but blocks no build.
    let mut prefix = library.to_owned();
    prefix.push(".");
    let runtime = identity.runtime.to_hex();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Ok(Ok(()));
    };
    for entry in entries.flatten() {
        let entry_name = entry.file_name();
        let Some(rest) = entry_name
            .as_encoded_bytes()
            .strip_prefix(prefix.as_encoded_bytes())
        else {
            continue;
        };
        // `<library hash>.<key>.o`, or that and `.<pid>` for an unfinished file.
        let hex64 = |b: &[u8]| b.len() == 64 && b.iter().all(u8::is_ascii_hexdigit);
        let (Some(made_from), Some(key), Some(tail)) =
            (rest.get(..64), rest.get(65..129), rest.get(129..))
        else {
            continue;
        };
        let finished = tail == b".o";
        let unfinished = tail
            .strip_prefix(b".o.")
            .is_some_and(|pid| !pid.is_empty() && pid.iter().all(u8::is_ascii_digit));
        let ours = hex64(made_from) && rest[64] == b'.' && hex64(key) && (finished || unfinished);
        let stale = made_from != runtime.as_bytes() || unfinished;
        if ours && stale && entry.path() != path {
            let _ = std::fs::remove_file(entry.path());
        }
    }
    Ok(Ok(()))
}

/// The error of a file `path` of the build of `out` that could not be written.
fn unwritable(path: &Path, e: &std::io::Error, out: &Path) -> (u8, String) {
    (
        1,
        format!(
            "zedc could not write {} while building {}: {e}. Repair: check that the directory \
             of {} exists and can be written, and that the disk has room",
            path.display(),
            out.display(),
            out.display()
        ),
    )
}

/// Whether the executable `out` can be kept as the link of `object` by the toolchain of
/// `identity`: the record beside it ([`Record`]) names the files its link read, the key of the
/// link with those files as they are now is the one `out` records as its build ID, and `out`'s
/// bytes are the ones the link wrote. No record, a file it names that cannot be read, another
/// key, or other bytes: it cannot, and the build links again. The cost is a hash of every
/// file the record names and of `out`, each once: linear in their bytes. A new file that appears
/// earlier on a search path, while every file the record names is unchanged, is not seen: the
/// limit of any cache that works from lists of the files a build read.
fn kept(out: &Path, identity: &Identity, object: &[u8], tools: &Toolchain) -> bool {
    let Some(record) = Record::read(out) else {
        return false;
    };
    let Ok(inputs) = Inputs::of(record.inputs, &[&tools.runtime]) else {
        return false;
    };
    let key = identity.key(object, &inputs.hashes);
    recorded(out).as_deref() == Some(key.as_bytes())
        && hash_file(out).is_ok_and(|h| h == record.output)
}

/// The BLAKE3 hash of the bytes of the file at `path`.
fn hash_file(path: &Path) -> Result<blake3::Hash, String> {
    let at = |e: std::io::Error| format!("{}: {e}", path.display());
    let mut hasher = blake3::Hasher::new();
    hasher
        .update_reader(std::fs::File::open(path).map_err(at)?)
        .map_err(at)?;
    Ok(hasher.finalize())
}

/// Replaces the build ID `partial` that a link wrote in the executable `exe` with `key`, in
/// place: the bytes of the note's descriptor, which nothing else in the file depends on. The
/// note is found by its section, and the descriptor in it by its bytes. False if `exe` has no
/// such note.
///
/// The note is found through a file opened only for reading, and the key is written by `dd`,
/// a process of its own (FAIL-l01-36b-link-identity-flake). A file this process held open for
/// writing would be held open, for writing, by each child another thread of this process forks
/// at that moment, until the child reaches exec; running `exe` while one such child has not,
/// which a loaded machine can delay by many milliseconds, fails with "Text file busy"
/// (ETXTBSY), in the build's caller or in any process that runs the output at once. A process
/// that runs builds on several threads and runs what they build, as the tests do, met it. The
/// cost is one spawn, about a millisecond, beside a link of a second or more.
fn write_build_id(exe: &Path, partial: &blake3::Hash, key: &blake3::Hash) -> Result<bool, String> {
    use object::{Object as _, ObjectSection as _};
    let at = |e: &dyn std::fmt::Display| format!("{}: {e}", exe.display());
    let mut file = std::fs::File::open(exe).map_err(|e| at(&e))?;
    let offset = {
        let cache = object::ReadCache::new(&mut file);
        let elf = object::File::parse(&cache).map_err(|e| at(&e))?;
        elf.section_by_name(".note.gnu.build-id").and_then(|note| {
            let (start, _) = note.file_range()?;
            let k = note
                .data()
                .ok()?
                .windows(blake3::OUT_LEN)
                .position(|w| w == partial.as_bytes())?;
            Some(start + k as u64)
        })
    };
    drop(file);
    let Some(offset) = offset else {
        return Ok(false);
    };
    // `bs=1` with `seek` and `count` in bytes, as POSIX defines them; `conv=notrunc` leaves
    // the rest of the file.
    let mut of = OsString::from("of=");
    of.push(exe);
    let mut dd = Command::new("dd")
        .arg(of)
        .args([
            "bs=1".to_string(),
            format!("seek={offset}"),
            format!("count={}", blake3::OUT_LEN),
            "conv=notrunc".to_string(),
        ])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| {
            format!(
                "zedc could not run `dd` to write the build ID of {} ({e}). Repair: install \
                 coreutils, which hold `dd`, or put the directory holding `dd` on PATH",
                exe.display()
            )
        })?;
    let wrote = dd.stdin.take().map(|mut s| s.write_all(key.as_bytes()));
    let done = dd.wait_with_output().map_err(|e| at(&e))?;
    match wrote {
        Some(Ok(())) if done.status.success() => Ok(true),
        _ => Err(at(&format!(
            "`dd` could not write the build ID ({}): {}",
            done.status,
            String::from_utf8_lossy(&done.stderr).trim_end()
        ))),
    }
}

/// The paths a linker's dependency file (`--dependency-file`) lists as the files it read, in
/// the order it lists them: a make rule, `<output>: \` followed by one line for each file,
/// each but the last ending in ` \`, then an empty line and a rule of its own for each file,
/// which is not read. GNU ld writes each path after two spaces, as it is; LLD writes each
/// after one space, with a space, `#` and `$` escaped. A path that names a file as it is
/// written is taken so; else it is read with LLD's escapes removed. A path holding a line
/// break cannot be listed in this form. One pass over the text.
pub fn dependencies(list: &[u8]) -> impl Iterator<Item = PathBuf> + '_ {
    use std::os::unix::ffi::OsStrExt as _;
    const TARGET_END: &[u8] = b": \\\n";
    let start = list
        .windows(TARGET_END.len())
        .position(|w| w == TARGET_END)
        .map(|k| k + TARGET_END.len());
    let mut more = start.is_some();
    list[start.unwrap_or(list.len())..]
        .split(|&b| b == b'\n')
        .map_while(move |line| {
            if !more {
                return None;
            }
            let line = line.strip_suffix(b" \\").unwrap_or_else(|| {
                more = false;
                line
            });
            let line = line.strip_prefix(b" ").unwrap_or(line);
            let line = line.strip_prefix(b" ").unwrap_or(line);
            let raw = Path::new(std::ffi::OsStr::from_bytes(line));
            if raw.symlink_metadata().is_ok() {
                return Some(raw.to_path_buf());
            }
            let mut path = Vec::with_capacity(line.len());
            let mut bytes = line.iter().peekable();
            while let Some(&b) = bytes.next() {
                match (b, bytes.peek()) {
                    (b'\\', Some(&&next)) if matches!(next, b' ' | b'#' | b'\\') => {
                        path.push(next);
                        bytes.next();
                    }
                    (b'$', Some(&&b'$')) => {
                        path.push(b'$');
                        bytes.next();
                    }
                    _ => path.push(b),
                }
            }
            Some(PathBuf::from(std::ffi::OsStr::from_bytes(&path)))
        })
}

/// The files a link read besides its object file and its runtime library, which the key
/// names by their bytes already: each named once, by the first of its paths in the order the
/// linker read them, with the BLAKE3 hash of its bytes, in the same order.
#[derive(Debug, PartialEq, Eq)]
pub struct Inputs {
    /// The paths.
    pub paths: Vec<PathBuf>,
    /// The hash of the file at each path.
    pub hashes: Vec<blake3::Hash>,
}

impl Inputs {
    /// The files at `paths` with their hashes, in order, but for a file named before by any
    /// path, and the files at `skip`. A file is told by its device and inode, so a file a
    /// linker reads more than once, or by two paths, is hashed once: the cost is linear in the
    /// number of paths and in the bytes of the distinct files. A path that cannot be opened
    /// or read is an error naming it.
    pub fn of(paths: impl IntoIterator<Item = PathBuf>, skip: &[&Path]) -> Result<Inputs, String> {
        use std::os::unix::fs::MetadataExt as _;
        let mut seen = std::collections::HashSet::new();
        for path in skip {
            if let Ok(m) = std::fs::metadata(path) {
                seen.insert((m.dev(), m.ino()));
            }
        }
        let mut inputs = Inputs {
            paths: Vec::new(),
            hashes: Vec::new(),
        };
        for path in paths {
            let at = |e: std::io::Error| format!("{}: {e}", path.display());
            let file = std::fs::File::open(&path).map_err(at)?;
            let m = file.metadata().map_err(at)?;
            if !seen.insert((m.dev(), m.ino())) {
                continue;
            }
            let mut hasher = blake3::Hasher::new();
            hasher.update_reader(file).map_err(at)?;
            inputs.hashes.push(hasher.finalize());
            inputs.paths.push(path);
        }
        Ok(inputs)
    }
}

/// What a link of `out` leaves beside it, at [`Record::path`]: the hash of the executable's
/// bytes as the link wrote them, and the paths of the files the link read ([`Inputs`]). A
/// later build reads it to find the files whose bytes its key needs before it can link, and
/// keeps `out` only if `out` still has those bytes: a stripped or edited executable keeps its
/// build ID, but not its hash. A file of its own, since a hash of the executable cannot be
/// held in the bytes it covers.
#[derive(Debug, PartialEq, Eq)]
pub struct Record {
    /// The BLAKE3 hash of the executable's bytes.
    pub output: blake3::Hash,
    /// The files the link read.
    pub inputs: Vec<PathBuf>,
}

impl Record {
    /// The first line of a record, which names its form.
    const FORM: &'static [u8] = b"zed-link 1\n";

    /// The record of the executable `out`: `<out>.zed-link`.
    pub fn path(out: &Path) -> PathBuf {
        let mut path = out.as_os_str().to_owned();
        path.push(".zed-link");
        PathBuf::from(path)
    }

    /// The record's bytes: `Record::FORM`, the output's hash in hexadecimal and a line
    /// break, then each path followed by a zero byte, which no path holds.
    pub fn to_bytes(&self) -> Vec<u8> {
        use std::os::unix::ffi::OsStrExt as _;
        let mut bytes = Self::FORM.to_vec();
        bytes.extend_from_slice(self.output.to_hex().as_bytes());
        bytes.push(b'\n');
        for path in &self.inputs {
            bytes.extend_from_slice(path.as_os_str().as_bytes());
            bytes.push(0);
        }
        bytes
    }

    /// The record of the executable `out`, if there is one and it has the form
    /// [`Record::to_bytes`] writes; `None` otherwise, and the build links again.
    pub fn read(out: &Path) -> Option<Record> {
        use std::os::unix::ffi::OsStrExt as _;
        let bytes = std::fs::read(Self::path(out)).ok()?;
        let rest = bytes.strip_prefix(Self::FORM)?;
        let (hex, rest) = rest.split_at_checked(64)?;
        let output = blake3::Hash::from_hex(hex).ok()?;
        let paths = rest.strip_prefix(b"\n")?;
        let inputs = if paths.is_empty() {
            Vec::new()
        } else {
            paths
                .strip_suffix(&[0])?
                .split(|&b| b == 0)
                .map(|p| PathBuf::from(std::ffi::OsStr::from_bytes(p)))
                .collect()
        };
        Some(Record { output, inputs })
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
                    "zedc cannot build {}: the path after `-o` names a directory, not a file. \
                     Repair: name the executable to write, as in `-o {}/program`",
                    out.display(),
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
            let failed = |e: std::io::Error| unwritable(&path, &e, out);
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
/// (see `Scratch`): each directory in `out`'s directory named `<out>.zed-build.<n>.<n>`,
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
            format!(
                "zedc cannot link an executable: the linker `{linker}` is missing. Repairs: \
                 install a C compiler, or name one in the environment variable CC"
            ),
        )
    } else {
        (
            1,
            format!(
                "zedc could not run the linker `{linker}`: {e}. Repair: name in the environment \
                 variable CC a C compiler that can be run"
            ),
        )
    }
}

/// What a link reads besides its object file (step L1.36b), each named by its content, not
/// by its path, so that a toolchain copied or reached by another path has the same identity
/// and a changed one has another.
///
/// - The linker is named by what its driver writes to standard output for `--version` and
///   for `-Wl,--version`: the driver's version and, through it, the linker's. Two spawns
///   that do no work, under 5 ms together.
/// - The runtime library is named by the BLAKE3 hash of its bytes: 0.11 to 0.20 s for its
///   227 MB (measured 2026-11-15, load 78), once per build. Its [`BUILD`] is not enough, since
///   it names the crate's Cargo configuration and not its source.
/// - The driver's environment is named by the values of [`DRIVER_ENV`] it runs with.
///
/// The other files the linker reads, the system libraries in `SYSTEM_LIBS`, the C start
/// files and `libgcc`, which the driver finds by itself and a system update can change under
/// one driver version, are known only from a link; [`Identity::key`] takes their hashes
/// ([`Inputs`]) from the link, or from the [`Record`] of the link before.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identity {
    /// The driver's standard output for `--version` and for `-Wl,--version`.
    pub linker: [Vec<u8>; 2],
    /// The BLAKE3 hash of the runtime library's bytes.
    pub runtime: blake3::Hash,
    /// The variables of [`DRIVER_ENV`] the driver runs with ([`Toolchain::env`]).
    pub env: Vec<(&'static str, Option<OsString>)>,
}

impl Identity {
    /// The identity of `tools`. A linker that cannot be run, fails to give its version or
    /// gives an empty one is an error, since links by two such linkers could not be told
    /// apart.
    pub fn of(tools: &Toolchain) -> Result<Identity, (u8, String)> {
        let linker = tools.linker.to_string_lossy();
        let version = |arg: &str| {
            let o = tools
                .driver()
                .arg(arg)
                .output()
                .map_err(|e| not_run(&linker, &e))?;
            if !o.status.success() {
                return Err((
                    1,
                    format!(
                        "zedc cannot use the linker `{linker}`: `{linker} {arg}` failed ({}), and zedc \
                         needs the linker's version to tell its links from another linker's. \
                         Repair: name in CC a C compiler that gives its version. The linker \
                         printed:\n{}",
                        o.status,
                        String::from_utf8_lossy(&o.stderr).trim_end()
                    ),
                ));
            }
            if o.stdout.is_empty() {
                return Err((
                    1,
                    format!(
                        "zedc cannot use the linker `{linker}`: it wrote nothing for `{linker} {arg}`, \
                         so its links cannot be told from another linker's. Repair: name in CC a \
                         C compiler that gives its version"
                    ),
                ));
            }
            Ok(o.stdout)
        };
        Ok(Identity {
            linker: [version("--version")?, version("-Wl,--version")?],
            runtime: hash_file(&tools.runtime).map_err(|e| (1, e))?,
            env: tools.env.clone(),
        })
    }

    /// The key of the link of `object` with the toolchain of this identity, which read the
    /// files of `inputs` ([`Inputs::hashes`]): a BLAKE3 hash of everything that enters the
    /// executable, which is the object file, this identity, the link's arguments other than
    /// the paths, and the bytes of the other files the linker read, in the order it read
    /// them, each preceded by its length. The link records it as the executable's GNU build
    /// ID, so that equal executables come from equal inputs, and a build whose output already
    /// records its key does not link again. Equal keys are taken for equal inputs with no
    /// comparison of the inputs, so the cache rests on BLAKE3's collision resistance
    /// (DESIGN.md sec:theories, the trusted base). Linear in the bytes of `object` and in the
    /// number of `inputs`.
    pub fn key(&self, object: &[u8], inputs: &[blake3::Hash]) -> blake3::Hash {
        let mut key = blake3::Hasher::new_derive_key(
            "zed-native 2026-11-15 the key of a link and the files it read",
        );
        let mut part = |bytes: &[u8]| {
            key.update(&bytes.len().to_le_bytes());
            key.update(bytes);
        };
        part(object);
        part(self.prelink_key().as_bytes());
        for a in SYSTEM_LIBS.iter().chain(LINK_FLAGS) {
            part(a.as_bytes());
        }
        part(&inputs.len().to_le_bytes());
        for input in inputs {
            part(input.as_bytes());
        }
        key.finalize()
    }

    /// The key of the prelinked runtime (`Prelinked`) of the toolchain of this identity: a
    /// BLAKE3 hash of this identity and of the prelink's arguments other than the paths,
    /// `PRELINK_FLAGS` and `roots`, each preceded by its length. The prelinked object's
    /// file name holds it, and [`Identity::key`] takes it in place of these parts.
    pub fn prelink_key(&self) -> blake3::Hash {
        use std::os::unix::ffi::OsStrExt as _;
        let mut key = blake3::Hasher::new_derive_key(
            "zed-native 2026-11-15 the key of a prelinked runtime library",
        );
        let mut part = |bytes: &[u8]| {
            key.update(&bytes.len().to_le_bytes());
            key.update(bytes);
        };
        part(self.runtime.as_bytes());
        for v in &self.linker {
            part(v);
        }
        for (name, value) in &self.env {
            part(name.as_bytes());
            match value {
                Some(value) => {
                    part(b"set");
                    part(value.as_bytes());
                }
                None => part(b"unset"),
            }
        }
        for a in PRELINK_FLAGS.iter().copied().chain(roots()) {
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
        "none of the runtime libraries in {} was built with {}, and code one build makes \
         does not run with another's library. Repair: build them together with `cargo build \
         -p zed-native`",
        dir.display(),
        exe.display()
    ))
}

/// The section of a file holding this crate that holds [`BUILD`].
pub const SECTION: &str = ".zed_native.build";

/// Which build of this crate a file holds: the runtime library, `zedc`, and any other
/// executable linked with this crate hold it as the bytes of [`SECTION`], which `strip` keeps,
/// unlike the symbol table. Two builds have equal bytes only if they agree in this crate's
/// hash, in the compiler's flags and in the sources of it and its workspace dependencies.
#[repr(C)]
pub struct Build {
    /// The identity of the type `Build`, which the compiler derives from this crate's hash:
    /// Cargo's hash of its features, its dependencies' builds, the profile, the target and
    /// the compiler.
    crate_hash: TypeId,
    /// A hash of the compiler's flags (`CARGO_ENCODED_RUSTFLAGS`), which the crate's hash
    /// leaves out; written by `build.rs`.
    rustflags: [u8; 8],
    /// The BLAKE3 hash of the sources of this crate and of the workspace crates it depends on
    /// ([`crate::sources`]), which the crate's hash leaves out; written by `build.rs`
    /// (RUNTIME-build-src).
    sources: [u8; 32],
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
    sources: include!(concat!(env!("OUT_DIR"), "/sources.rs")),
};

/// The bytes of [`SECTION`] in the executable or object file `exe`: the [`BUILD`] of the
/// zed-native it holds.
pub fn build_id(exe: &Path) -> Result<Vec<u8>, String> {
    let file = std::fs::File::open(exe).map_err(|e| format!("{}: {e}", exe.display()))?;
    let cache = object::ReadCache::new(file);
    section(&cache, exe)?.ok_or_else(|| {
        format!(
            "{} is not zedc or a file built with it: it has no section {SECTION}, where \
             every build of zed-native names itself, so the runtime library built with it \
             cannot be found",
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

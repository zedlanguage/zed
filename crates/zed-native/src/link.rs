//! `zedc build <file> -o <out>` (step L1.36a): the program's code, compiled to an object file
//! as step L1.36 compiles it, linked with the runtime library into an executable that binds
//! its ports from its own command line as `zedc run` does.
//!
//! The runtime library is this crate built as a static library, `libzed_native.a`, which
//! Cargo writes beside the `zedc` executable; the linker is the system's C compiler driver.
//! The link records no time, build path or random value, so two builds of one program give
//! the same bytes.

use std::ffi::OsString;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

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
    let program = zedc::run::load_file(file, stderr)?;
    let g = Arc::new(lower(&program.term()).map_err(|e| (1, format!("{file}: {e}")))?);
    let object = crate::executable_object(&g, &plan(&g, true), program.ports())
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

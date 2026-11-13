//! An executable's start (step L1.36a): the object file `zedc build` links holds the program's
//! code, the program as data, and a C `main` that passes both, with its own command line, to
//! [`zed_main`] in the runtime library.
//!
//! The data is the plan's `fuse` flag, the program's content address, which a record names
//! (step L1.19b), `main`'s ports as [`Ports::to_text`] writes them, and the graph as lowered in
//! ZIR's binary form; and for the run-time errors' sites (plan row RT-sites), the name of the
//! source file, its text and the site of each node of the graph. The runtime decodes the graph, legalizes it and plans it again, which
//! gives the tables the code was generated from, node for node, and the nodes legalization
//! swapped: the code passes node numbers, and the hooks read the tables by them.

use std::ffi::{CStr, OsString, c_char, c_int};
use std::io::Write as _;
use std::os::unix::ffi::OsStringExt as _;
use std::sync::Arc;

use cranelift_codegen::ir::types::I32;
use cranelift_codegen::ir::{AbiParam, InstBuilder};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};

use zedc::address::ContentAddress;
use zedc::run::Ports;
use zedc::zir::Region;
use zedc::zir::legalize::{Legalized, legalized_sites};
use zedc::zir::memory::{Plan, plan};

use zed_kernel::sites::Span;
use zed_rt::Word;

use crate::tables::Tables;

/// The program an executable runs: what its data holds, decoded and legalized.
struct Program {
    ports: Ports,
    /// The content address of the program built, which a record names (step L1.19b).
    address: ContentAddress,
    graph: Legalized,
    plan: Plan,
    /// The program's source text and the name of its file, which an error's site is placed in.
    text: String,
    file: Option<String>,
    /// The site of each node of `graph`, by its number, when it has one.
    sites: Vec<Option<Span>>,
}

/// `text` with every line that no site in `sites` touches emptied, its line break kept, and
/// each site moved by the bytes removed before it: the lines an error can be printed on, at
/// the same line numbers and columns. An executable holds only the branch its build takes
/// (DESIGN.md step L2.8d), so it holds the lines of the operations staging kept and not the
/// rest of the source, where a dropped branch's text would be; text of a dropped branch
/// written on a line with a kept operation is held, as part of that line.
// Complexity tradeoff: O(s + n log l) for s bytes of source, n sites and l lines: the line
// starts in one pass, each site's first and last line by binary search, the touched lines
// marked by a difference array (a site that spans many lines costs two entries, not one per
// line), and the bytes removed before each line summed in one pass. Keeping whole lines
// rather than only the sites' own bytes is what lets the line be printed as `zedc run`
// prints it. Test: `exe::tests::an_executable_keeps_the_lines_of_its_sites_only`,
// `l02_08d_build_constant::staged`.
fn kept_lines(text: &str, sites: &[Option<Span>]) -> (String, Vec<Option<Span>>) {
    let starts: Vec<usize> = std::iter::once(0)
        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
        .collect();
    let line = |at: usize| starts.partition_point(|&s| s <= at) - 1;
    let mut touched = vec![0i64; starts.len() + 1];
    for s in sites.iter().flatten() {
        let last = if s.end > s.start { s.end - 1 } else { s.start };
        touched[line(s.start.min(text.len()))] += 1;
        touched[line(last.min(text.len())) + 1] -= 1;
    }
    let (mut out, mut removed, mut depth) = (String::new(), Vec::with_capacity(starts.len()), 0);
    for (k, &start) in starts.iter().enumerate() {
        depth += touched[k];
        removed.push(start - out.len());
        let end = starts.get(k + 1).copied().unwrap_or(text.len());
        if depth > 0 {
            out.push_str(&text[start..end]);
        } else if k + 1 < starts.len() {
            out.push('\n');
        }
    }
    let moved = sites
        .iter()
        .map(|s| {
            s.map(|s| {
                let by = removed[line(s.start.min(text.len()))];
                Span {
                    start: s.start - by,
                    end: s.end - by,
                }
            })
        })
        .collect();
    (out, moved)
}

/// The bytes of the data: `fuse` as one byte, the program's content address as its 32 bytes,
/// the length of the ports' text as 8 bytes, little end first, the text; the source file's name
/// (empty for none) and the lines of the source text the sites touch ([`kept_lines`]), each the
/// same way; the number of sites in 8 bytes and each site as its start and end in 8 bytes each,
/// both [`u64::MAX`] for a node with none, by node number in `graph`, as
/// [`lower_sited`](zedc::zir::lower::lower_sited) numbers them;
/// then the graph. An error when the system refuses the memory to write one of the graph's
/// exact numbers, or the memory of the data, which is asked before it is written.
// Complexity tradeoff: the executable holds the source lines the sites touch, one byte for each
// other line, and 16 bytes a node, O(s + n) bytes at most for s bytes of source and n nodes,
// written and read once, so that a run-time error prints the source line as `zedc run` does
// with no file beside the executable. The line and column alone would cost less and could not
// print the line; the sites are stored in full, not delta coded as DWARF's line table is
// (DWARF 5, section 6.2), since the graph beside them takes O(n) bytes already. Test:
// `exe::tests::the_data_reads_back`, `l01_36a_executables::sites`.
pub(crate) fn data(
    fuse: bool,
    address: ContentAddress,
    ports: &Ports,
    source: (Option<&str>, &str),
    sites: &[Option<Span>],
    graph: &Region,
) -> Result<Vec<u8>, String> {
    let text = ports.to_text();
    let file = source.0.unwrap_or_default();
    let (source, sites) = kept_lines(source.1, sites);
    let source = source.as_str();
    let zir = zedc::zir::binary::encode(graph).map_err(|e| {
        format!(
            "zedc could not build the executable: a constant of the program is so large that \
             the system refused the {} bytes of memory needed to write it into the executable. \
             Repairs: free memory and build again, or run the program with `zedc run`, which \
             writes no executable",
            zed_kernel::num::bytes_of(&e.bits)
        )
    })?;
    let len =
        1 + 32 + 8 * 4 + text.len() + file.len() + source.len() + 16 * sites.len() + zir.len();
    let mut out = Vec::new();
    out.try_reserve_exact(len).map_err(|_| {
        format!(
            "zedc could not build the executable: the program's data in it is {len} bytes, and \
             the system refused that much memory. Repairs: free memory and build again, or run \
             the program with `zedc run`, which writes no executable"
        )
    })?;
    out.push(u8::from(fuse));
    out.extend_from_slice(&address.0);
    out.extend_from_slice(&(text.len() as u64).to_le_bytes());
    out.extend_from_slice(text.as_bytes());
    for s in [file, source] {
        out.extend_from_slice(&(s.len() as u64).to_le_bytes());
        out.extend_from_slice(s.as_bytes());
    }
    out.extend_from_slice(&(sites.len() as u64).to_le_bytes());
    for s in &sites {
        let (start, end) = s.map_or((u64::MAX, u64::MAX), |s| (s.start as u64, s.end as u64));
        out.extend_from_slice(&start.to_le_bytes());
        out.extend_from_slice(&end.to_le_bytes());
    }
    out.extend_from_slice(&zir);
    Ok(out)
}

/// The message of an executable whose stored program cannot be read back.
const DAMAGED: &str = "this executable cannot run: the program stored in it is damaged, so the file \
                       was changed after `zedc build` wrote it. Repair: build it again with \
                       `zedc build`";

impl Program {
    /// The program `data` holds, as [`data`] writes it, legalized for this back end.
    fn decode(data: &[u8]) -> Result<Program, String> {
        let bad = || DAMAGED.to_string();
        let (&fuse, rest) = data.split_first().ok_or_else(bad)?;
        let (address, rest) = rest.split_first_chunk::<32>().ok_or_else(bad)?;
        let address = ContentAddress(*address);
        let (text, rest) = string(rest).ok_or_else(bad)?;
        let ports = Ports::from_text(text)?;
        let (file, rest) = string(rest).ok_or_else(bad)?;
        let (source, rest) = string(rest).ok_or_else(bad)?;
        let (n, mut zir) = number(rest).ok_or_else(bad)?;
        // Each site is 16 bytes, so a count the data cannot hold is refused before any memory
        // is asked for it.
        if n > zir.len() / 16 {
            return Err(bad());
        }
        let mut sites = Vec::with_capacity(n);
        for _ in 0..n {
            let (start, rest) = number(zir).ok_or_else(bad)?;
            let (end, rest) = number(rest).ok_or_else(bad)?;
            zir = rest;
            sites.push((start != usize::MAX).then_some(Span { start, end }));
        }
        let graph = zedc::zir::binary::decode(zir).map_err(|e| format!("{DAMAGED} ({e})"))?;
        let sites = legalized_sites(&graph, crate::legal::EXPANSIONS, &sites);
        let graph = crate::legal::legalize(graph);
        let plan = plan(graph.graph(), fuse != 0);
        Ok(Program {
            ports,
            address,
            graph,
            plan,
            text: source.to_owned(),
            file: (!file.is_empty()).then(|| file.to_owned()),
            sites,
        })
    }
}

/// The number in the first 8 bytes of `data`, little end first, and the bytes after them.
fn number(data: &[u8]) -> Option<(usize, &[u8])> {
    let (n, rest) = data.split_first_chunk::<8>()?;
    Some((usize::try_from(u64::from_le_bytes(*n)).ok()?, rest))
}

/// The text whose length in bytes the first 8 bytes of `data` give, and the bytes after it.
fn string(data: &[u8]) -> Option<(&str, &[u8])> {
    let (n, rest) = number(data)?;
    let (text, rest) = rest.split_at_checked(n)?;
    Some((std::str::from_utf8(text).ok()?, rest))
}

/// Defines, in `m`, the data `data` and a C `main(argc, argv)` that returns
/// `zed_main(argc, argv, data, its length, root)`.
pub(crate) fn define_main<M: Module>(m: &mut M, root: FuncId, data: &[u8]) -> Result<(), String> {
    let err = |e: cranelift_module::ModuleError| crate::bug::bug(e);
    let at = m
        .declare_data("zed_program", Linkage::Local, false, false)
        .map_err(err)?;
    let mut d = DataDescription::new();
    d.define(data.into());
    m.define_data(at, &d).map_err(err)?;
    let ptr = m.target_config().pointer_type();
    let mut start = m.make_signature();
    start.params = [I32, ptr, ptr, ptr, ptr].map(AbiParam::new).to_vec();
    start.returns.push(AbiParam::new(I32));
    let zed_main = m
        .declare_function("zed_main", Linkage::Import, &start)
        .map_err(err)?;
    let mut ctx = m.make_context();
    ctx.func.signature.params = [I32, ptr].map(AbiParam::new).to_vec();
    ctx.func.signature.returns.push(AbiParam::new(I32));
    let main = m
        .declare_function("main", Linkage::Export, &ctx.func.signature)
        .map_err(err)?;
    let mut fbc = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let (argc, argv) = (b.block_params(entry)[0], b.block_params(entry)[1]);
        let gv = m.declare_data_in_func(at, b.func);
        let data_at = b.ins().symbol_value(ptr, gv);
        let len = b.ins().iconst(ptr, data.len() as i64);
        let root = m.declare_func_in_func(root, b.func);
        let root = b.ins().func_addr(ptr, root);
        let callee = m.declare_func_in_func(zed_main, b.func);
        let call = b.ins().call(callee, &[argc, argv, data_at, len, root]);
        let status = b.inst_results(call)[0];
        b.ins().return_(&[status]);
        b.finalize(m.isa().frontend_config());
    }
    m.define_function(main, &mut ctx).map_err(err)?;
    m.clear_context(&mut ctx);
    Ok(())
}

/// The runtime's start: runs the program in the `len` bytes at `data` on the command line
/// `argv`, its code entered at `root`, and returns the exit status `zedc run` gives.
#[unsafe(no_mangle)]
#[expect(
    unsafe_code,
    reason = "the generated `main` calls the runtime by this symbol"
)]
pub extern "C" fn zed_main(
    argc: c_int,
    argv: *const *const c_char,
    data: *const u8,
    len: usize,
    root: extern "C" fn() -> Word,
) -> c_int {
    let argc = usize::try_from(argc).unwrap_or(0);
    // SAFETY: the C runtime passes `argc` pointers to NUL-ended strings in `argv`, and the
    // generated `main` passes its own data with that data's length.
    #[expect(unsafe_code, reason = "C's `main` gives its arguments as pointers")]
    let (words, data) = unsafe {
        let words: Vec<OsString> = (0..argc)
            .map(|i| OsString::from_vec(CStr::from_ptr(*argv.add(i)).to_bytes().to_vec()))
            .collect();
        (words, std::slice::from_raw_parts(data, len))
    };
    let status = start(&words, data, root);
    // Rust flushes standard output when its own `main` returns; this `main` is C's.
    let _ = std::io::stdout().flush();
    c_int::from(status)
}

/// Runs the program in `data` on the command line `words`, the first word the executable's
/// name, and gives the exit status.
fn start(words: &[OsString], data: &[u8], root: extern "C" fn() -> Word) -> u8 {
    // A panic is a broken check of zedc's own code: say so in the program's terms, not as
    // Rust's panic text alone (DESIGN.md sec:diagnostics).
    std::panic::set_hook(Box::new(|info| {
        let _ = writeln!(
            std::io::stderr(),
            "{}",
            zed_rt::bug(
                "reached a state that zedc's own checks rule out",
                &info.to_string()
            )
        );
    }));
    let (mut stdin, mut stdout, mut stderr) =
        (std::io::stdin(), std::io::stdout(), std::io::stderr());
    let program = match Program::decode(data) {
        Ok(p) => p,
        Err(e) => {
            let _ = writeln!(stderr, "{e}");
            return 1;
        }
    };
    let name = words
        .first()
        .map_or_else(|| "program".into(), |w| w.to_string_lossy().into_owned());
    zedc::run::executable(
        &name,
        &program.ports,
        program.address,
        words.get(1..).unwrap_or_default(),
        &mut stdin,
        &mut stdout,
        &mut stderr,
        |ev| {
            let (t, _) = Tables::new(&program.graph, &program.plan)?;
            crate::outcome::call(Arc::new(t), root, ev)
                .map(|o| o.value)
                // The error printed as `zedc run` prints it, at the site of the node that
                // raised it (plan row RT-sites).
                .map_err(|(why, at)| {
                    let at = at.and_then(|i| program.sites.get(i).copied().flatten());
                    zedc::run::placed(&program.text, program.file.as_deref(), why, at)
                })
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc::run::PortKind;

    #[test]
    fn an_executable_keeps_the_lines_of_its_sites_only() {
        // Lines 2 and 4 to 5 hold sites; lines 1, 3 and 6 are emptied, their line breaks kept,
        // so each site keeps its line and column.
        let text = "dropped one\nkept a + b\ndropped two\nkept (c\n  + d)\ndropped three";
        let at = |s: &str| text.find(s).unwrap();
        let sites = [
            Some(Span {
                start: at("a + b"),
                end: at("a + b") + 5,
            }),
            None,
            Some(Span {
                start: at("(c"),
                end: at("d)") + 2,
            }),
        ];
        let (kept, moved) = kept_lines(text, &sites);
        assert_eq!(kept, "\nkept a + b\n\nkept (c\n  + d)\n");
        assert!(!kept.contains("dropped"));
        let site = |k: usize| moved[k].map(|s| &kept[s.start..s.end]);
        assert_eq!(
            (site(0), site(1), site(2)),
            (Some("a + b"), None, Some("(c\n  + d)"))
        );
        // The same lines and columns in both texts.
        let place = |t: &str, s: usize| {
            let before = &t[..s];
            (
                before.matches('\n').count(),
                s - before.rfind('\n').map_or(0, |i| i + 1),
            )
        };
        for (k, s) in sites.iter().enumerate() {
            if let (Some(s), Some(m)) = (s, moved[k]) {
                assert_eq!(place(text, s.start), place(&kept, m.start));
            }
        }
        // No sites: every line emptied.
        assert_eq!(
            kept_lines(text, &[None]),
            ("\n\n\n\n\n".to_string(), vec![None])
        );
    }

    #[test]
    fn the_data_reads_back() {
        let ports = Ports {
            inputs: vec![
                ("stdin".into(), PortKind::Lines),
                ("fs".into(), PortKind::Files),
                ("args".into(), PortKind::CommandLine),
                ("env".into(), PortKind::Env),
            ],
            outputs: vec!["stdout".into(), "log".into()],
        };
        // `"a" > "b"`: the start legalizes the graph as the build does, so its swapped node
        // is known again and a refusal there names `>`.
        use zed_kernel::term::{Prim, build::lit};
        let graph = zedc::zir::lower::lower(&zed_kernel::term::build::prim(
            Prim::Gt,
            vec![lit("a"), lit("b")],
        ))
        .unwrap();
        let address = ContentAddress([7; 32]);
        let site = Some(Span { start: 1, end: 4 });
        let source = (Some("a.zed"), "x = \"a\" > \"b\";");
        let p = Program::decode(&data(true, address, &ports, source, &[site], &graph).unwrap())
            .unwrap();
        assert_eq!((p.file.as_deref(), p.text.as_str()), source);
        assert_eq!(p.sites, [site]);
        assert_eq!(p.ports, ports);
        assert_eq!(p.address, address);
        let built = crate::legal::legalize(graph.clone());
        assert_eq!(p.graph.graph(), built.graph());
        assert_eq!(p.graph.swapped(), built.swapped());
        assert!(p.graph.swapped().contains(0));
        assert!(p.plan.fuse);
        let bytes = data(false, address, &ports, (None, ""), &[None], &graph).unwrap();
        let p = Program::decode(&bytes).unwrap();
        assert!(!p.plan.fuse);
        assert_eq!((p.file, p.text.as_str(), p.sites), (None, "", vec![None]));
        // Cut in the flag, the address, the length, at the text and in it.
        for cut in [0, 1, 5, 37, 41, 44] {
            assert_eq!(
                Program::decode(&bytes[..cut]).err().as_deref(),
                Some(DAMAGED),
                "cut at {cut}"
            );
        }
    }
}

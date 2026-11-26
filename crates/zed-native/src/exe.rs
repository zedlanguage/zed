//! An executable's start (step L1.36a): the object file `zedc build` links holds the program's
//! code, the program as data, and a C `main` that passes both, with its own command line, to
//! [`zed_main`] in the runtime library.
//!
//! The data is the program's content address, which a record names (step L1.19b), `main`'s
//! ports as [`Ports::to_text`] writes them, the limits written before `main` as
//! [`MainLimits::to_text`] writes them; for the run-time errors' sites (plan row RT-sites), the
//! name of the source file, its text and the site of each node of the graph; the memory plan the
//! code was made from ([`Plan::to_bytes`]); and the graph as lowered in ZIR's binary form. The
//! runtime decodes the graph and legalizes it, which gives the nodes legalization swapped, and
//! reads the plan, checked against the legalized graph ([`Plan::from_bytes`]), instead of
//! planning again (plan row EXE-plan-carried; DESIGN.md sec:kernel, "Facts carried, and the
//! stripped form"): with them, the tables the code was generated from, node for node, since the
//! code passes node numbers and the hooks read the tables by them.

use std::ffi::{CStr, OsString, c_char, c_int};
use std::io::Write as _;
use std::os::unix::ffi::OsStringExt as _;
#[cfg(target_os = "linux")]
use std::path::Path;
use std::sync::Arc;

use cranelift_codegen::ir::types::I32;
use cranelift_codegen::ir::{AbiParam, InstBuilder};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};

use zedc::address::ContentAddress;
use zedc::run::Ports;
use zedc::zir::Region;
use zedc::zir::legalize::{Legalized, legalized_sites};
use zedc::zir::memory::Plan;

use zed_kernel::limits::MainLimits;
use zed_kernel::sites::Span;
use zed_rt::Word;

use crate::codegen::Code;
use crate::tables::Tables;

/// The program an executable runs: what its data holds, decoded and legalized.
struct Program {
    ports: Ports,
    /// The limits written before `main`, which the start sets on its own process.
    limits: MainLimits,
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
    // Cannot panic: `starts[0] == 0 <= at`, so `line(at)` is in `0..starts.len()`, and
    // `touched` has `starts.len() + 1` entries and `removed` one per start; `start <= end <=
    // text.len()`, each just after a `\n` or at an end, so a character boundary.
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

/// The bytes of the data: the program's content address as its 32 bytes,
/// the length of the ports' text as 8 bytes, little end first, the text; the limits' text
/// the same way; the source file's name
/// (empty for none) and the lines of the source text the sites touch ([`kept_lines`]), each the
/// same way; the number of sites in 8 bytes and each site as its start and end in 8 bytes each,
/// both [`u64::MAX`] for a node with none, by node number in `graph`, as
/// [`lower_sited`](zedc::zir::lower::lower_sited) numbers them; `plan`, the memory plan of
/// `graph` legalized, which carries `fuse`, as [`Plan::to_bytes`] writes it, after its length
/// in 8 bytes;
/// then the graph in its stripped binary form ([`zedc::zir::strip`]), which keeps what running
/// needs and none of the facts kept for checking: the executable runs the program and is not
/// re-checked, and stripping keeps the node numbers the sites use. An error when the system
/// refuses the memory to write one of the graph's exact numbers, or the memory of the data,
/// which is asked before it is written.
// Complexity tradeoff: the executable holds the source lines the sites touch, one byte for each
// other line, and 16 bytes a node, O(s + n) bytes at most for s bytes of source and n nodes,
// written and read once, so that a run-time error prints the source line as `zedc run` does
// with no file beside the executable. The line and column alone would cost less and could not
// print the line; the sites are stored in full, not delta coded as DWARF's line table is
// (DWARF 5, section 6.2), since the graph beside them takes O(n) bytes already. Test:
// `exe::tests::the_data_reads_back`, `l01_36a_executables::sites`.
pub(crate) fn data(
    plan: &Plan,
    address: ContentAddress,
    ports: &Ports,
    limits: &MainLimits,
    source: (Option<&str>, &str),
    sites: &[Option<Span>],
    graph: &Region,
) -> Result<Vec<u8>, String> {
    let text = ports.to_text();
    let limits = limits.to_text();
    let file = source.0.unwrap_or_default();
    let (source, sites) = kept_lines(source.1, sites);
    let source = source.as_str();
    let zir = zedc::zir::strip::encode_stripped(graph).map_err(|e| {
        format!(
            "Executable too large for memory: writing a constant of the program into the \
             executable takes {}. Repairs: free memory and build again, or run the program with \
             `zedc run`, which writes no executable",
            e.memory()
        )
    })?;
    let plan = plan.to_bytes();
    let len = 32
        + 8 * 6
        + text.len()
        + limits.len()
        + file.len()
        + source.len()
        + 16 * sites.len()
        + plan.len()
        + zir.len();
    let mut out = Vec::new();
    out.try_reserve_exact(len).map_err(|_| {
        format!(
            "Executable too large for memory: the program's data in it takes {}. Repairs: free \
             memory and build again, or run the program with `zedc run`, which writes no \
             executable",
            zed_kernel::num::TooLarge::of_bytes(len).memory()
        )
    })?;
    out.extend_from_slice(&address.0);
    out.extend_from_slice(&(text.len() as u64).to_le_bytes());
    out.extend_from_slice(text.as_bytes());
    for s in [limits.as_str(), file, source] {
        out.extend_from_slice(&(s.len() as u64).to_le_bytes());
        out.extend_from_slice(s.as_bytes());
    }
    out.extend_from_slice(&(sites.len() as u64).to_le_bytes());
    for s in &sites {
        let (start, end) = s.map_or((u64::MAX, u64::MAX), |s| (s.start as u64, s.end as u64));
        out.extend_from_slice(&start.to_le_bytes());
        out.extend_from_slice(&end.to_le_bytes());
    }
    out.extend_from_slice(&(plan.len() as u64).to_le_bytes());
    out.extend_from_slice(&plan);
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
        let (address, rest) = data.split_first_chunk::<32>().ok_or_else(bad)?;
        let address = ContentAddress(*address);
        let (text, rest) = string(rest).ok_or_else(bad)?;
        let ports = Ports::from_text(text)?;
        let (limits, rest) = string(rest).ok_or_else(bad)?;
        let limits = MainLimits::from_text(limits).map_err(|e| format!("{DAMAGED} ({e})"))?;
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
        let (n, rest) = number(zir).ok_or_else(bad)?;
        let (plan, zir) = rest.split_at_checked(n).ok_or_else(bad)?;
        // The data holds the stripped form; a full one would run the same.
        let (graph, _) =
            zedc::zir::binary::decode_form(zir).map_err(|e| format!("{DAMAGED} ({e})"))?;
        // The decoder checks the bytes, not that each input names an argument or an earlier
        // node's output that exists (`binary.rs`, `decode`); legalization and the tables index
        // by those, so a changed file would stop the start with a panic instead of this
        // message (TEST-runtime-panic-guard). O(size of the graph), as the decode is.
        zedc::zir::validate::validate(&graph).map_err(|e| format!("{DAMAGED} ({e})"))?;
        let sites = legalized_sites(&graph, crate::legal::EXPANSIONS, &sites);
        let graph = crate::legal::legalize(graph);
        // The plan the code was made from, read and not worked out again; its counts and
        // indices are checked against the graph, and `Plan::recheck` plans again to compare.
        let plan = Plan::from_bytes(plan, graph.graph()).map_err(|e| format!("{DAMAGED} ({e})"))?;
        Ok(Program {
            ports,
            limits,
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

/// The section of an executable `zedc build` writes that holds the program as data (`data`),
/// and nothing else: the data is the only thing the build puts in it, and a linker joins
/// sections of one name from its inputs, of which only the build's object file has one. A
/// section of its own name, so that `check` finds the data by that name, also in a stripped
/// executable, which has lost its symbol table and so the symbol `zed_program`, as
/// [`crate::link::build_id`] finds the build of the runtime.
pub const PROGRAM_SECTION: &str = ".zed_program";

/// The message of an executable whose stored memory plan is read without fault but is not the
/// plan its graph gives.
#[cfg(target_os = "linux")]
const NOT_ITS_PLAN: &str = "this executable's memory plan is not the plan its program gives, \
                            so the file was changed after `zedc build` wrote it, and run as it \
                            is it may free memory the program still uses, or never free it. \
                            Repair: build it again with `zedc build`";

/// `zedc check-exe <file>` (plan row EXE-plan-carried-recheck): whether the executable `exe`
/// holds a program its start can read ([`Program::decode`]) and a memory plan that is the plan
/// of its graph ([`Plan::recheck`]). The start of an executable does not run this check, by
/// decision: it reads the plan and does not work it out again (DESIGN.md sec:kernel, "Facts
/// carried, and the stripped form": no runtime works a fact out again), and the re-check costs
/// a planning of the graph, which is what reading the plan saves (benchmark
/// `l01_36a_executables::bench::the_start_reads_the_plan_in_less_work_than_planning`). Why no
/// check cheaper than planning can run at the start instead, in order of growth: planning is
/// O(occurrences + edges) ([`zedc::zir::memory::plan`]), and an exact check of a stored plan
/// must confirm, for each edge, its drop or last use, which is a claim that no later node of
/// the region uses the edge. A check that leaves some use of an edge unread accepts the same
/// plan for the graph with that use moved after the claimed last use, where the plan frees
/// the edge too early; so an exact check reads every use of every edge, Ω(occurrences +
/// edges), the order of planning itself. A cheaper check could differ from planning only by a
/// constant factor, and this one, a planning and a comparison, is exact.
// Complexity tradeoff: O(b) to read the file's `b` bytes and the section, plus the cost of
// `Program::decode` (O(size of the data)) and of `Plan::recheck` (a planning, O(occurrences +
// edges), and a comparison linear in the plan). Test: `l01_36a_executables::plan_carried::
// the_check_of_an_executable_refuses_each_damage_its_start_reads`.
#[cfg(target_os = "linux")]
pub fn check(exe: &Path) -> Result<(), String> {
    let not_one = |why: &str| {
        format!(
            "this file is not an executable `zedc build` wrote: {why}. Repair: name the file \
             `zedc build <file> -o <out>` wrote as <out>"
        )
    };
    match crate::section::section_of(exe, PROGRAM_SECTION) {
        Ok(Some(data)) => check_data(&data),
        Ok(None) => Err(not_one(&format!(
            "it has no section {PROGRAM_SECTION}, which holds the program"
        ))),
        Err(why) => Err(not_one(&why)),
    }
}

/// The check of [`check`] on the program's data `data`.
#[cfg(target_os = "linux")]
fn check_data(data: &[u8]) -> Result<(), String> {
    let p = Program::decode(data)?;
    (p.plan.recheck(p.graph.graph())).map_err(|why| format!("{NOT_ITS_PLAN} ({why})"))
}

/// `zedc check-exe` with the words `args` after `check-exe`: runs `check` on the one file
/// they name and gives the exit status, 0 when the check passes (and nothing is printed), 1
/// when it refuses the file, with the reason written to `stderr`, and 2 when `args` is not one
/// word.
#[cfg(target_os = "linux")]
pub fn check_command(args: &[String], stderr: &mut dyn std::io::Write) -> u8 {
    let [file] = args else {
        let _ = writeln!(
            stderr,
            "`zedc check-exe` takes one word after it, the executable to check, and was given \
             {} words. Write `zedc check-exe <file>`, once for each file.",
            args.len()
        );
        return 2;
    };
    match check(Path::new(file)) {
        Ok(()) => 0,
        Err(why) => {
            let _ = writeln!(stderr, "{file}: {why}");
            1
        }
    }
}

/// The bytes of one function's entry in the table of the program's code ([`define_code`]).
const FUNCTION_BYTES: usize = 32;

/// The bytes of one range of a node's code in that table.
const RANGE_BYTES: usize = 12;

/// Defines, in `m`, the table `zed_code` of the program's code, for the map of a fault to the
/// node whose code it is in (plan row RT-internal-fault): the number of functions in 8 bytes,
/// then for each its address (relocated by the linker), its length, the index of its first
/// range and its number of ranges, 8 bytes each; then each range as its start and end, offsets
/// in the function, and the node's number, 4 bytes each. All numbers little end first, as
/// the hosts zedc builds for are (x86_64 and AArch64 Linux). Read by [`code_functions`].
// Complexity tradeoff: O(f + r) bytes for f functions and r ranges, a table beside the code
// as DWARF's line table is (DWARF 5, section 6.2), not delta coded, since the graph's data
// already costs O(n) bytes; the ranges only, not the lines and columns, which the handler
// finds at a fault from the sites the data holds. Test:
// `l01_36a_executables::internal_fault`.
fn define_code<M: Module>(m: &mut M, code: &[Code]) -> Result<DataId, String> {
    let err = |e: cranelift_module::ModuleError| crate::bug::bug(e);
    let ranges: usize = code.iter().map(|c| c.nodes.len()).sum();
    let mut bytes = Vec::with_capacity(8 + FUNCTION_BYTES * code.len() + RANGE_BYTES * ranges);
    bytes.extend_from_slice(&(code.len() as u64).to_le_bytes());
    let mut first = 0u64;
    for c in code {
        let n = c.nodes.len() as u64;
        for x in [0, u64::from(c.len), first, n] {
            bytes.extend_from_slice(&x.to_le_bytes());
        }
        first += n;
    }
    for &(s, e, k) in code.iter().flat_map(|c| &c.nodes) {
        for x in [s, e, k] {
            bytes.extend_from_slice(&x.to_le_bytes());
        }
    }
    let at = m
        .declare_data("zed_code", Linkage::Local, false, false)
        .map_err(err)?;
    let mut d = DataDescription::new();
    d.define(bytes.into());
    d.set_align(8);
    for (i, c) in code.iter().enumerate() {
        let f = m.declare_func_in_data(c.id, &mut d);
        d.write_function_addr((8 + FUNCTION_BYTES * i) as u32, f);
    }
    m.define_data(at, &d).map_err(err)?;
    Ok(at)
}

/// The functions of the table [`define_code`] wrote at `code`.
///
/// # Safety
///
/// `code` is the address of `zed_code` in this executable, as its `main` passes it.
#[expect(
    unsafe_code,
    reason = "the table is read through the address the linker gave it"
)]
unsafe fn code_functions(code: *const u8) -> Vec<zed_rt::code::Function> {
    // SAFETY: the caller's contract: the table is as `define_code` wrote it, its functions'
    // addresses relocated, and every read below is within it. Read unaligned, so that no
    // claim on the linker's placement is made past the table's own alignment.
    unsafe {
        let word = |at: usize| u64::from_le(code.add(at).cast::<u64>().read_unaligned()) as usize;
        let half = |at: usize| u32::from_le(code.add(at).cast::<u32>().read_unaligned());
        let n = word(0);
        let ranges = 8 + FUNCTION_BYTES * n;
        (0..n)
            .map(|i| {
                let f = 8 + FUNCTION_BYTES * i;
                let (first, count) = (word(f + 16), word(f + 24));
                zed_rt::code::Function {
                    start: word(f),
                    len: word(f + 8),
                    nodes: (first..first + count)
                        .map(|j| {
                            let r = ranges + RANGE_BYTES * j;
                            (half(r), half(r + 4), half(r + 8))
                        })
                        .collect(),
                }
            })
            .collect()
    }
}

/// Defines, in `m`, the data `data`, the table of the program's code `code` ([`define_code`])
/// and a C `main(argc, argv)` that returns `zed_main(argc, argv, data, its length, root,
/// the table)`, and gives `main`'s code: its length and, when `unwind`, its call frame
/// information, for [`crate::dwarf::eh_frame`].
pub(crate) fn define_main<M: Module>(
    m: &mut M,
    root: FuncId,
    data: &[u8],
    code: &[Code],
    unwind: bool,
) -> Result<Code, String> {
    let err = |e: cranelift_module::ModuleError| crate::bug::bug(e);
    let at = m
        .declare_data("zed_program", Linkage::Local, false, false)
        .map_err(err)?;
    let mut d = DataDescription::new();
    d.define(data.into());
    d.set_custom_section(PROGRAM_SECTION);
    m.define_data(at, &d).map_err(err)?;
    let table = define_code(m, code)?;
    let ptr = m.target_config().pointer_type();
    let mut start = m.make_signature();
    start.params = [I32, ptr, ptr, ptr, ptr, ptr].map(AbiParam::new).to_vec();
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
        // Cannot panic: `main`'s signature, set above, has the two parameters.
        let (argc, argv) = (b.block_params(entry)[0], b.block_params(entry)[1]);
        let gv = m.declare_data_in_func(at, b.func);
        let data_at = b.ins().symbol_value(ptr, gv);
        let len = b.ins().iconst(ptr, data.len() as i64);
        let root = m.declare_func_in_func(root, b.func);
        let root = b.ins().func_addr(ptr, root);
        let gv = m.declare_data_in_func(table, b.func);
        let table = b.ins().symbol_value(ptr, gv);
        let callee = m.declare_func_in_func(zed_main, b.func);
        let call = b
            .ins()
            .call(callee, &[argc, argv, data_at, len, root, table]);
        let status = b.inst_results(call)[0]; // Cannot panic: `zed_main` returns one value.
        b.ins().return_(&[status]);
        b.finalize(m.isa().frontend_config());
    }
    m.define_function(main, &mut ctx).map_err(err)?;
    let c = (ctx.compiled_code()).ok_or_else(|| crate::bug::bug("`main` compiled to no code"))?;
    let unwind = match unwind {
        true => c.create_unwind_info(m.isa()).map_err(crate::bug::bug)?,
        false => None,
    };
    let main = Code {
        id: main,
        len: c.code_info().total_size,
        nodes: Vec::new(),
        unwind,
        vars: Vec::new(),
    };
    m.clear_context(&mut ctx);
    Ok(main)
}

/// The runtime's start: runs the program in the `len` bytes at `data` on the command line
/// `argv`, its code entered at `root` and described by the table at `code`
/// ([`define_code`]), and returns the exit status `zedc run` gives.
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
    code: *const u8,
) -> c_int {
    let argc = usize::try_from(argc).unwrap_or(0);
    // SAFETY: the C runtime passes `argc` pointers to NUL-ended strings in `argv`, and the
    // generated `main` passes its own data with that data's length, and its table of code.
    #[expect(unsafe_code, reason = "C's `main` gives its arguments as pointers")]
    let (words, data, code) = unsafe {
        let words: Vec<OsString> = (0..argc)
            .map(|i| OsString::from_vec(CStr::from_ptr(*argv.add(i)).to_bytes().to_vec()))
            .collect();
        (
            words,
            std::slice::from_raw_parts(data, len),
            code_functions(code),
        )
    };
    // A write to a pipe whose reader has closed it is a failed write of the port, which the
    // run reports with status 1 as `zedc run` does (DESIGN.md sec:ports: the first `#ioError`
    // aborts the wave), and not a stop by SIGPIPE with no message. Rust's own `main`, which
    // `zedc` has, ignores SIGPIPE before it runs; this `main` is C's, so the start does it. A
    // child the program starts gets SIGPIPE back at its default, as Rust's `Command` resets it.
    // SAFETY: `signal` with `SIG_IGN` installs no handler and touches no memory of Rust's.
    #[expect(unsafe_code, reason = "signal is a libc call")]
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_IGN);
    }
    let status = start(&words, data, root, code);
    // Rust flushes standard output when its own `main` returns; this `main` is C's. Flushed
    // before the runtime closes descriptors 1 and 2, whose failure turns a status of 0 into 1
    // (step L7.3p).
    let _ = std::io::stdout().flush();
    c_int::from(zed_rt::close::standard_streams(status))
}

/// Runs the program in `data` on the command line `words`, the first word the executable's
/// name, its code the functions `code`, and gives the exit status.
fn start(
    words: &[OsString],
    data: &[u8],
    root: extern "C" fn() -> Word,
    code: Vec<zed_rt::code::Function>,
) -> u8 {
    // A panic is a broken check of zedc's own code: reported as `zedc run` reports one in a
    // run, and the process ends with status 3 from the hook, before the panic unwinds into a
    // runtime hook or `zed_main`, where it would abort (plan row EXE-panic-status).
    std::panic::set_hook(Box::new(|info| {
        zedc::run::stop_at_bug(info, zed_rt::close::standard_streams)
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
    // The limits hold from here: the decoded program is the executable's, not the run's.
    if let Err(e) = zed_rt::limits::enforce(&program.limits) {
        let _ = writeln!(stderr, "{e}");
        return 1;
    }
    let name = words
        .first()
        .map_or_else(|| "program".into(), |w| w.to_string_lossy().into_owned());
    // A fault in the code that no rule explains is reported as a bug in zedc, with the
    // program's address and the site of the node whose code faulted (plan row
    // RT-internal-fault).
    let map = zed_rt::code::CodeMap::new(
        &program.address.to_string(),
        program.file.as_deref(),
        &program.text,
        program.sites.iter().map(|s| s.map(|s| s.start)).collect(),
        code,
    );
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
            crate::outcome::call(Arc::new(t), root, ev, Some(&map))
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
        let limits = MainLimits {
            memory: Some(1 << 30),
            cpu: Some(std::time::Duration::from_millis(500)),
            ..MainLimits::default()
        };
        let plan_of = |g: &Region, fuse| {
            zedc::zir::memory::plan(crate::legal::legalize(g.clone()).graph(), fuse)
        };
        let plan = plan_of(&graph, true);
        let bytes = data(&plan, address, &ports, &limits, source, &[site], &graph).unwrap();
        let p = Program::decode(&bytes).unwrap();
        // The plan is read, not worked out again, and is the one the build made.
        assert_eq!(p.plan, plan);
        assert_eq!(p.limits, limits);
        assert_eq!((p.file.as_deref(), p.text.as_str()), source);
        assert_eq!(p.sites, [site]);
        assert_eq!(p.ports, ports);
        assert_eq!(p.address, address);
        // The data holds the graph stripped, and the start legalizes that.
        let built = crate::legal::legalize(zedc::zir::strip::strip(&graph));
        assert_eq!(p.graph.graph(), built.graph());
        assert_eq!(p.graph.swapped(), built.swapped());
        assert!(p.graph.swapped().contains(0));
        assert!(p.plan.fuse);
        // The plan of another graph, `"a" > "b" > "c"`, is refused against this one.
        let other = zedc::zir::lower::lower(&zed_kernel::term::build::prim(
            Prim::Gt,
            vec![
                zed_kernel::term::build::prim(Prim::Gt, vec![lit("a"), lit("b")]),
                lit("c"),
            ],
        ))
        .unwrap();
        let wrong = data(
            &plan_of(&other, true),
            address,
            &ports,
            &limits,
            source,
            &[site],
            &graph,
        );
        let refused = Program::decode(&wrong.unwrap()).err().unwrap();
        assert!(refused.starts_with(DAMAGED), "{refused}");
        assert!(refused.contains("of the memory plan"), "{refused}");
        // A graph whose input names a node the region does not have, as a changed file can
        // hold it, is refused, not indexed by (TEST-runtime-panic-guard).
        let mut bad = graph.clone();
        bad.nodes[0].inputs[0] = zedc::zir::Src::Out(5, 0);
        let wrong = data(&plan, address, &ports, &limits, source, &[site], &bad);
        let refused = Program::decode(&wrong.unwrap()).err().unwrap();
        assert!(refused.starts_with(DAMAGED), "{refused}");
        let bytes = data(
            &plan_of(&graph, false),
            address,
            &ports,
            &MainLimits::default(),
            (None, ""),
            &[None],
            &graph,
        )
        .unwrap();
        let p = Program::decode(&bytes).unwrap();
        assert!(!p.plan.fuse);
        assert!(p.limits.is_none());
        assert_eq!((p.file, p.text.as_str(), p.sites), (None, "", vec![None]));
        // Cut in the address, the length, at the text and in it, in the length of the limits,
        // and in the graph, at the end, whose message names the byte.
        let limits_at = 32 + 8 + ports.to_text().len();
        let cut = Program::decode(&bytes[..bytes.len() - 1]).err().unwrap();
        assert!(cut.starts_with(DAMAGED), "{cut}");
        for cut in [0, 1, 5, 31, 36, 40, 43, limits_at + 3] {
            assert_eq!(
                Program::decode(&bytes[..cut]).err().as_deref(),
                Some(DAMAGED),
                "cut at {cut}"
            );
        }
    }
}

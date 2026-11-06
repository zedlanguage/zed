//! An executable's start (step L1.36a): the object file `zedc build` links holds the program's
//! code, the program as data, and a C `main` that passes both, with its own command line, to
//! [`zed_main`] in the runtime library.
//!
//! The data is the plan's `fuse` flag, the program's content address, which a record names
//! (step L1.19b), `main`'s ports as [`Ports::to_text`] writes them, and the graph as lowered in
//! ZIR's binary form. The runtime decodes the graph, legalizes it and plans it again, which
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
use zedc::zir::legalize::Legalized;
use zedc::zir::memory::{Plan, plan};

use zed_rt::Word;

use crate::tables::Tables;

/// The program an executable runs: what its data holds, decoded and legalized.
struct Program {
    ports: Ports,
    /// The content address of the program built, which a record names (step L1.19b).
    address: ContentAddress,
    graph: Legalized,
    plan: Plan,
}

/// The bytes of the data: `fuse` as one byte, the program's content address as its 32 bytes,
/// the length of the ports' text as 8 bytes, little end first, the text, then the graph. An
/// error when the system refuses the memory to write one of the graph's exact numbers.
pub(crate) fn data(
    fuse: bool,
    address: ContentAddress,
    ports: &Ports,
    graph: &Region,
) -> Result<Vec<u8>, String> {
    let text = ports.to_text();
    let mut out = vec![u8::from(fuse)];
    out.extend_from_slice(&address.0);
    out.extend_from_slice(&(text.len() as u64).to_le_bytes());
    out.extend_from_slice(text.as_bytes());
    let zir = zedc::zir::binary::encode(graph).map_err(|e| {
        format!(
            "a constant is so large that the system refused the {} bytes of memory asked to \
             write it into the executable",
            zed_kernel::num::bytes_of(&e.bits)
        )
    })?;
    out.extend_from_slice(&zir);
    Ok(out)
}

impl Program {
    /// The program `data` holds, as [`data`] writes it, legalized for this back end.
    fn decode(data: &[u8]) -> Result<Program, String> {
        let bad = || "the program data of this executable is damaged".to_string();
        let (&fuse, rest) = data.split_first().ok_or_else(bad)?;
        let (address, rest) = rest.split_first_chunk::<32>().ok_or_else(bad)?;
        let address = ContentAddress(*address);
        let (len, rest) = rest.split_first_chunk::<8>().ok_or_else(bad)?;
        let len = usize::try_from(u64::from_le_bytes(*len)).map_err(|_| bad())?;
        let (text, zir) = rest.split_at_checked(len).ok_or_else(bad)?;
        let text = std::str::from_utf8(text).map_err(|_| bad())?;
        let ports = Ports::from_text(text)?;
        let graph = crate::legalize(zedc::zir::binary::decode(zir)?);
        let plan = plan(graph.graph(), fuse != 0);
        Ok(Program {
            ports,
            address,
            graph,
            plan,
        })
    }
}

/// Defines, in `m`, the data `data` and a C `main(argc, argv)` that returns
/// `zed_main(argc, argv, data, its length, root)`.
pub(crate) fn define_main<M: Module>(m: &mut M, root: FuncId, data: &[u8]) -> Result<(), String> {
    let err = |e: cranelift_module::ModuleError| format!("native: {e}");
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
            crate::call(Arc::new(t), root, ev).map(|o| o.value)
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use zedc::run::PortKind;

    #[test]
    fn the_data_reads_back() {
        let ports = Ports {
            inputs: vec![
                ("stdin".into(), PortKind::Lines),
                ("fs".into(), PortKind::Files),
                ("args".into(), PortKind::CommandLine),
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
        let p = Program::decode(&data(true, address, &ports, &graph).unwrap()).unwrap();
        assert_eq!(p.ports, ports);
        assert_eq!(p.address, address);
        let built = crate::legalize(graph.clone());
        assert_eq!(p.graph.graph(), built.graph());
        assert_eq!(p.graph.swapped(), built.swapped());
        assert!(p.graph.swapped().contains(0));
        assert!(p.plan.fuse);
        let bytes = data(false, address, &ports, &graph).unwrap();
        assert!(!Program::decode(&bytes).unwrap().plan.fuse);
        // Cut in the flag, the address, the length, at the text and in it.
        for cut in [0, 1, 5, 37, 41, 44] {
            assert_eq!(
                Program::decode(&bytes[..cut]).err().as_deref(),
                Some("the program data of this executable is damaged"),
                "cut at {cut}"
            );
        }
    }
}

//! DWARF 5 for the object file of an executable (plan row DEBUG-dwarf-clif, zed/DEBUGGING.md
//! sections 4 and 5): one compilation unit for the program's file, a line table with an
//! `is_stmt` row where the source line changes, from the node sites the executable keeps
//! (plan row RT-sites), and a `DW_TAG_subprogram` for each function the generator defines. The
//! call frame information is `.eh_frame` ([`eh_frame`]), from Cranelift's unwind information
//! for each function, in every executable.
//!
//! The sections are added to the object after its code is made, so the code bytes are the same
//! with and without them (test `l01_36a_executables::dwarf`). Addresses are relocations against
//! each function's symbol, and offsets between the debug sections are relocations against the
//! target section's symbol, since the linker places these sections after the runtime library's.
//!
//! On x86-64 a debug build also defines the thread-local `zed_debug_task` and
//! `zed_debug_keypath` of zed/DEBUGGING.md section 6 and describes them ([`DebugVars`]), so a
//! breakpoint can be conditioned on the task. They hold their first values, task 0 and the
//! root's keypath (empty), for the whole run: the serial runtime runs one instance of each
//! region, the root's. A real task number, and a keypath set at the start of each region
//! instance, need the parallel runtime.
//!
//! Not yet emitted (DEBUG-dwarf-clif-bindings): bindings and parameters, their types, columns,
//! and source names for the functions; each subprogram is named by its symbol (`zed_body_3`).
//! No inlined calls are described, since the generator inlines none: each function of the
//! graph is a function of the object, and only primitives are emitted in place.

use cranelift_codegen::isa::unwind::UnwindInfo;
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use cranelift_object::object::write::{
    Relocation as ObjectRelocation, SectionId as ObjectSection, StandardSection,
};
use cranelift_object::object::{RelocationEncoding, RelocationFlags, RelocationKind, SectionKind};
use cranelift_object::{ObjectModule, ObjectProduct};
use gimli::write::{
    Address, AttributeValue, CommonInformationEntry, DwarfUnit, EhFrame, EndianVec, Expression,
    FrameTable, LineProgram, LineString, Range, RangeList, RelocateWriter, Relocation,
    RelocationTarget, Sections,
};
use gimli::{Encoding, Format, LineEncoding, RunTimeEndian};

use zed_kernel::sites::Span;
use zedc::source::Lines;

use crate::bug::bug;
use crate::codegen::Code;

/// `DW_AT_language`: the first code DWARF leaves to languages it does not list
/// (`DW_LANG_lo_user`, DWARF 5 section 7.12, table 7.17). gdb reads an unknown code as its
/// "minimal" language, whose expressions are C's; the tests `l01_36a_executables::dwarf`
/// check that `print` and a breakpoint conditioned on `zed_debug_task` work under it
/// (zed/DEBUGGING.md section 4: "chosen by test").
pub(crate) const LANGUAGE: gimli::DwLang = gimli::DW_LANG_lo_user;

/// The name `DW_AT_producer` gives.
const PRODUCER: &str = "zedc";

/// One line-table row of a function: the offset of its first byte from the function's start,
/// its 1-based source line (0 for code of no site), whether it starts a statement
/// (`is_stmt`), and whether it ends the prologue (`prologue_end`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub offset: u32,
    pub line: u32,
    pub stmt: bool,
    pub prologue_end: bool,
}

/// The rows of a function whose code for each node is `nodes`, `(start, end, node)` sorted by
/// start ([`Code::nodes`]), and whose node `k` is on line `line_of(k)`, or on none.
///
/// A row starts at each node range whose line differs from the row before; a statement starts
/// where the line differs from the last line with a number, so code of no site between two
/// ranges of one line (line 0, `is_stmt` false, LLVM's rule for code of no line) does not make
/// a second statement there. The code before the first node with a line, the prologue, is
/// given that node's line, and a second row of that line at the node ends the prologue: gdb
/// places a function's breakpoint at the `prologue_end` row, or else at the second row of the
/// function's first line. A function with no node on a line has no rows.
///
/// O(r) for r node ranges, besides the calls of `line_of`.
pub(crate) fn rows(nodes: &[(u32, u32, u32)], line_of: impl Fn(u32) -> Option<u32>) -> Vec<Row> {
    let mut out: Vec<Row> = Vec::new();
    let mut last_line = 0;
    let mut end = 0;
    for &(start, stop, node) in nodes {
        let Some(line) = line_of(node).filter(|&l| l > 0) else {
            continue;
        };
        if out.is_empty() {
            if start > 0 {
                out.push(Row {
                    offset: 0,
                    line,
                    stmt: true,
                    prologue_end: false,
                });
            }
            out.push(Row {
                offset: start,
                line,
                stmt: true,
                prologue_end: start > 0,
            });
        } else {
            if start > end {
                out.push(Row {
                    offset: end,
                    line: 0,
                    stmt: false,
                    prologue_end: false,
                });
            }
            let prev = out.last().unwrap().line;
            if prev != line {
                out.push(Row {
                    offset: start,
                    line,
                    stmt: line != last_line,
                    prologue_end: false,
                });
            }
        }
        last_line = line;
        end = end.max(stop);
    }
    out
}

/// A debug section as gimli writes it, with the relocations it asks for.
#[derive(Clone)]
struct Section {
    writer: EndianVec<RunTimeEndian>,
    relocations: Vec<Relocation>,
}

impl RelocateWriter for Section {
    type Writer = EndianVec<RunTimeEndian>;

    fn writer(&self) -> &Self::Writer {
        &self.writer
    }

    fn writer_mut(&mut self) -> &mut Self::Writer {
        &mut self.writer
    }

    fn relocate(&mut self, relocation: Relocation) {
        self.relocations.push(relocation);
    }
}

/// The thread-local variables of a debug build (zed/DEBUGGING.md section 6): `zed_debug_task`,
/// an unsigned 64-bit task number, and `zed_debug_keypath`, a pointer to a C string.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DebugVars {
    task: DataId,
    keypath: DataId,
}

/// Defines in `m` the thread-local variables of a debug build, on x86-64; `None` on another
/// target, whose thread-local relocation in DWARF ([`add`]) is not written yet.
///
/// `zed_debug_task` is 0 in `.tbss` and `zed_debug_keypath` points at an empty string, the
/// root's keypath. No code writes them: the serial runtime runs only the root's instance, task
/// 0; a real task number, and a keypath set at the start of each region instance, need the
/// parallel runtime (plan row DEBUG-dwarf-clif). Each is kept in a section of its own marked
/// `SHF_GNU_RETAIN` (cranelift-object's `used`), as the link's `--gc-sections` keeps only
/// sections reached from code, and a relocation from a debug section does not count.
pub(crate) fn define_debug_vars(m: &mut ObjectModule) -> Result<Option<DebugVars>, String> {
    if !cfg!(target_arch = "x86_64") {
        return Ok(None);
    }
    let err = |e: cranelift_module::ModuleError| bug(e);
    let root =
        (m.declare_data("zed_debug_keypath_root", Linkage::Local, false, false)).map_err(err)?;
    let mut d = DataDescription::new();
    d.define(Box::new([0u8]));
    d.set_used(true);
    m.define_data(root, &d).map_err(err)?;
    let task = (m.declare_data("zed_debug_task", Linkage::Export, true, true)).map_err(err)?;
    let mut d = DataDescription::new();
    d.define_zeroinit(8);
    d.set_align(8);
    d.set_used(true);
    m.define_data(task, &d).map_err(err)?;
    let keypath =
        (m.declare_data("zed_debug_keypath", Linkage::Export, true, true)).map_err(err)?;
    let mut d = DataDescription::new();
    d.define(Box::new([0u8; 8]));
    d.set_align(8);
    d.set_used(true);
    let at = m.declare_data_in_data(root, &mut d);
    d.write_data_addr(0, at, 0);
    m.define_data(keypath, &d).map_err(err)?;
    Ok(Some(DebugVars { task, keypath }))
}

/// Adds the DWARF of the functions `code`, named `names` (one name each, in the same order),
/// to `product`: the program's file `file`, its working directory `dir`, its text `text`, the
/// site of each node of the legalized graph, by its number, `sites`, and the thread-local
/// variables `vars` ([`define_debug_vars`]).
///
/// A thread-local variable's location is `DW_OP_const8u <offset> DW_OP_form_tls_address`, its
/// offset in the module's thread-local block a `R_X86_64_DTPOFF64` relocation, as GCC writes
/// it. gimli writes no relocated `DW_OP_const8u`, so the expression is written with
/// `DW_OP_addr`, whose operand is the same 8 bytes, and the opcode byte is changed after: a
/// debugger adds the executable's load address to a `DW_OP_addr` operand, which an offset must
/// not get.
///
/// O(T + r log L + f) for a text of T bytes in L lines, r node ranges and f functions: the line
/// starts are found once ([`Lines`]), each range's line by binary search, and each section is
/// written once. Bench `l01_36a_executables::bench::the_dwarf_of_n_statements_scales`.
#[expect(
    clippy::too_many_arguments,
    reason = "each is a separate input of the DWARF, passed once by `executable_object`"
)]
pub(crate) fn add(
    product: &mut ObjectProduct,
    code: &[Code],
    names: &[String],
    file: &str,
    dir: &str,
    text: &str,
    sites: &[Option<Span>],
    vars: Option<DebugVars>,
) -> Result<(), String> {
    let address_size = u8::try_from(std::mem::size_of::<usize>()).map_err(bug)?;
    let encoding = Encoding {
        format: Format::Dwarf32,
        version: 5,
        address_size,
    };
    // gimli refuses an empty name; a program read from standard input has none.
    let file = if file.is_empty() { "<stdin>" } else { file };
    let dir = if dir.is_empty() { "." } else { dir };
    let lines = Lines::new(text.as_bytes());
    let line_of = |node: u32| {
        let s = sites.get(usize::try_from(node).ok()?).copied().flatten()?;
        u32::try_from(lines.line_start(s.start).1).ok()
    };
    let mut lp = LineProgram::new(
        encoding,
        LineEncoding::default(),
        LineString::String(dir.as_bytes().to_vec()),
        None,
        LineString::String(file.as_bytes().to_vec()),
        None,
    );
    let file_id = lp.add_file(
        LineString::String(file.as_bytes().to_vec()),
        lp.default_directory(),
        None,
    );
    let mut dwarf = DwarfUnit::new(encoding);
    // gimli's symbol numbers index `symbols`, the object's symbol of each function.
    let mut symbols = Vec::with_capacity(code.len());
    let mut ranges = Vec::with_capacity(code.len());
    let root = dwarf.unit.root();
    for (c, name) in code.iter().zip(names) {
        let at = Address::Symbol {
            symbol: symbols.len(),
            addend: 0,
        };
        symbols.push(product.function_symbol(c.id));
        ranges.push(Range::StartLength {
            begin: at,
            length: u64::from(c.len),
        });
        let rows = rows(&c.nodes, line_of);
        if !rows.is_empty() {
            lp.begin_sequence(Some(at));
            for r in &rows {
                let row = lp.row();
                row.address_offset = u64::from(r.offset);
                row.file = file_id;
                row.line = u64::from(r.line);
                row.column = 0;
                row.is_statement = r.stmt;
                row.prologue_end = r.prologue_end;
                lp.generate_row();
            }
            lp.end_sequence(u64::from(c.len));
        }
        let sub = dwarf.unit.add(root, gimli::DW_TAG_subprogram);
        let e = dwarf.unit.get_mut(sub);
        e.set(
            gimli::DW_AT_name,
            AttributeValue::String(name.as_bytes().to_vec()),
        );
        e.set(gimli::DW_AT_low_pc, AttributeValue::Address(at));
        e.set(
            gimli::DW_AT_high_pc,
            AttributeValue::Udata(u64::from(c.len)),
        );
        if name == "zed_root" {
            e.set(gimli::DW_AT_external, AttributeValue::FlagPresent);
        }
        if let Some(r) = rows.iter().find(|r| r.line > 0) {
            e.set(
                gimli::DW_AT_decl_file,
                AttributeValue::FileIndex(Some(file_id)),
            );
            e.set(
                gimli::DW_AT_decl_line,
                AttributeValue::Udata(u64::from(r.line)),
            );
        }
    }
    // gimli's symbol numbers of the thread-local variables, whose relocations are offsets in
    // the thread-local block.
    let mut tls = Vec::new();
    if let Some(v) = vars {
        let base = |dwarf: &mut DwarfUnit, name: &str, ate: gimli::DwAte, size: u64| {
            let t = dwarf.unit.add(root, gimli::DW_TAG_base_type);
            let e = dwarf.unit.get_mut(t);
            e.set(gimli::DW_AT_name, AttributeValue::String(name.into()));
            e.set(gimli::DW_AT_encoding, AttributeValue::Encoding(ate));
            e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(size));
            t
        };
        let word = base(&mut dwarf, "u64", gimli::DW_ATE_unsigned, 8);
        let byte = base(&mut dwarf, "char", gimli::DW_ATE_signed_char, 1);
        let string = dwarf.unit.add(root, gimli::DW_TAG_pointer_type);
        let e = dwarf.unit.get_mut(string);
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(byte));
        e.set(
            gimli::DW_AT_byte_size,
            AttributeValue::Udata(u64::from(address_size)),
        );
        for (name, id, ty) in [
            ("zed_debug_task", v.task, word),
            ("zed_debug_keypath", v.keypath, string),
        ] {
            let mut location = Expression::new();
            location.op_addr(Address::Symbol {
                symbol: symbols.len(),
                addend: 0,
            });
            location.op(gimli::DW_OP_form_tls_address);
            tls.push(symbols.len());
            symbols.push(product.data_symbol(id));
            let var = dwarf.unit.add(root, gimli::DW_TAG_variable);
            let e = dwarf.unit.get_mut(var);
            e.set(gimli::DW_AT_name, AttributeValue::String(name.into()));
            e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
            e.set(gimli::DW_AT_external, AttributeValue::FlagPresent);
            e.set(gimli::DW_AT_location, AttributeValue::Exprloc(location));
        }
    }
    dwarf.unit.line_program = lp;
    let list = dwarf.unit.ranges.add(RangeList(ranges));
    let e = dwarf.unit.get_mut(root);
    e.set(
        gimli::DW_AT_producer,
        AttributeValue::String(PRODUCER.into()),
    );
    e.set(gimli::DW_AT_language, AttributeValue::Language(LANGUAGE));
    e.set(gimli::DW_AT_name, AttributeValue::String(file.into()));
    e.set(gimli::DW_AT_comp_dir, AttributeValue::String(dir.into()));
    e.set(
        gimli::DW_AT_low_pc,
        AttributeValue::Address(Address::Constant(0)),
    );
    e.set(gimli::DW_AT_ranges, AttributeValue::RangeListRef(list));
    let mut sections = Sections::new(Section {
        writer: EndianVec::new(endian()),
        relocations: Vec::new(),
    });
    dwarf.write(&mut sections).map_err(bug)?;
    // Each section gimli wrote, with its relocations. There are about 20 kinds of section, so
    // the searches of `placed` below are O(1) each.
    let mut written: Vec<(gimli::SectionId, Vec<u8>, Vec<Relocation>)> = Vec::new();
    sections.for_each(|id, s| -> Result<(), String> {
        written.push((id, s.writer.slice().to_vec(), s.relocations.clone()));
        Ok(())
    })?;
    // Each thread-local variable's `DW_OP_addr` becomes `DW_OP_const8u`, its operand an offset
    // in the thread-local block (see above).
    for (_, bytes, relocations) in &mut written {
        for r in relocations.iter() {
            if !matches!(r.target, RelocationTarget::Symbol(k) if tls.contains(&k)) {
                continue;
            }
            let op = (r.offset.checked_sub(1)).and_then(|o| bytes.get_mut(o));
            match op {
                Some(b) if *b == gimli::DW_OP_addr.0 && r.size == 8 => {
                    *b = gimli::DW_OP_const8u.0;
                }
                _ => return Err(bug("a thread-local variable's location is not DW_OP_addr")),
            }
        }
    }
    // Every section with bytes, and every one a relocation names, gets an object section before
    // any relocation is added, since a relocation may name a section written after its own.
    let obj = &mut product.object;
    let mut placed: Vec<(gimli::SectionId, ObjectSection)> = Vec::new();
    let mut place = |obj: &mut cranelift_object::object::write::Object<'static>,
                     id: gimli::SectionId| {
        if let Some(&(_, k)) = placed.iter().find(|(g, _)| *g == id) {
            return k;
        }
        let k = obj.add_section(
            Vec::new(),
            id.name().as_bytes().to_vec(),
            SectionKind::Debug,
        );
        placed.push((id, k));
        k
    };
    for (id, bytes, relocations) in &written {
        if bytes.is_empty() && relocations.is_empty() {
            continue;
        }
        let k = place(&mut *obj, *id);
        obj.set_section_data(k, bytes.clone(), 1);
    }
    for (id, _, relocations) in written {
        for r in relocations {
            let at = place(&mut *obj, id);
            let symbol = match r.target {
                RelocationTarget::Symbol(k) => symbols[k],
                RelocationTarget::Section(t) => {
                    let t = place(&mut *obj, t);
                    obj.section_symbol(t)
                }
            };
            if matches!(r.target, RelocationTarget::Symbol(k) if tls.contains(&k)) {
                obj.add_relocation(
                    at,
                    ObjectRelocation {
                        offset: u64::try_from(r.offset).map_err(bug)?,
                        symbol,
                        addend: r.addend,
                        flags: RelocationFlags::Elf {
                            r_type: cranelift_object::object::elf::R_X86_64_DTPOFF64,
                        },
                    },
                )
                .map_err(bug)?;
                continue;
            }
            add_relocation(obj, at, r.offset, symbol, r.addend, r.size)?;
        }
    }
    Ok(())
}

/// Adds to `product` the section `.eh_frame`: under the common entry `cie`, the call frame
/// information of each function of `code` that has it ([`Code::unwind`]). Nothing when the
/// target has no System V entry (`cie` is `None`) or no function has the information.
///
/// Each function's start is written relative to its field (`DW_EH_PE_pcrel | DW_EH_PE_sdata4`,
/// an `R_X86_64_PC32` relocation on x86-64), as a C compiler writes it, and not as an
/// absolute address: `.eh_frame` is read-only in the executable, so a position-independent
/// executable cannot link an absolute relocation there (ld.lld: "relocation R_X86_64_64 cannot
/// be used against symbol 'zed_root'; recompile with -fPIC"). Cranelift's own `.eh_frame`
/// (cranelift-object 0.137.1 `unwind.rs`, `ObjectBuilder::unwind_info`) writes the absolute
/// form, since the common entry `isa.create_systemv_cie()` makes keeps gimli's default
/// `fde_address_encoding`, `DW_EH_PE_absptr` (gimli 0.33.0 `write/cfi.rs`:147), which is why
/// this does not use it.
///
/// O(f + u) for f functions whose unwind information has u instructions in all: each entry is
/// written once.
pub(crate) fn eh_frame<'c>(
    product: &mut ObjectProduct,
    cie: Option<CommonInformationEntry>,
    code: impl Iterator<Item = &'c Code>,
) -> Result<(), String> {
    let Some(mut cie) = cie else {
        return Ok(());
    };
    cie.fde_address_encoding = gimli::DW_EH_PE_pcrel | gimli::DW_EH_PE_sdata4;
    let mut table = FrameTable::default();
    let cie = table.add_cie(cie);
    // gimli's symbol numbers index `symbols`, the object's symbol of each function.
    let mut symbols = Vec::new();
    for c in code {
        let Some(UnwindInfo::SystemV(u)) = &c.unwind else {
            continue;
        };
        let at = Address::Symbol {
            symbol: symbols.len(),
            addend: 0,
        };
        symbols.push(product.function_symbol(c.id));
        table.add_fde(cie, u.to_fde(at));
    }
    if symbols.is_empty() {
        return Ok(());
    }
    let mut eh = EhFrame(Section {
        writer: EndianVec::new(endian()),
        relocations: Vec::new(),
    });
    table.write_eh_frame(&mut eh).map_err(bug)?;
    let EhFrame(s) = eh;
    let obj = &mut product.object;
    let at = obj.section_id(StandardSection::EhFrame);
    let align = u64::try_from(std::mem::size_of::<usize>()).map_err(bug)?;
    obj.append_section_data(at, s.writer.slice(), align);
    for r in s.relocations {
        let RelocationTarget::Symbol(k) = r.target else {
            return Err(bug(".eh_frame asked for a relocation against a section"));
        };
        let pcrel = r.eh_pe.map(|pe| pe.application()) == Some(gimli::DW_EH_PE_pcrel);
        let kind = match pcrel {
            true => RelocationKind::Relative,
            false => RelocationKind::Absolute,
        };
        obj.add_relocation(
            at,
            ObjectRelocation {
                offset: u64::try_from(r.offset).map_err(bug)?,
                symbol: symbols[k],
                addend: r.addend,
                flags: RelocationFlags::Generic {
                    kind,
                    encoding: RelocationEncoding::Generic,
                    size: r.size * 8,
                },
            },
        )
        .map_err(bug)?;
    }
    Ok(())
}

/// The host's byte order, as gimli names it.
fn endian() -> RunTimeEndian {
    if cfg!(target_endian = "little") {
        RunTimeEndian::Little
    } else {
        RunTimeEndian::Big
    }
}

/// Adds to `obj`'s section `at` an absolute relocation of `size` bytes at `offset`, to
/// `symbol` plus `addend`.
fn add_relocation(
    obj: &mut cranelift_object::object::write::Object<'static>,
    at: ObjectSection,
    offset: usize,
    symbol: cranelift_object::object::write::SymbolId,
    addend: i64,
    size: u8,
) -> Result<(), String> {
    obj.add_relocation(
        at,
        ObjectRelocation {
            offset: u64::try_from(offset).map_err(bug)?,
            symbol,
            addend,
            flags: RelocationFlags::Generic {
                kind: RelocationKind::Absolute,
                encoding: RelocationEncoding::Generic,
                size: size * 8,
            },
        },
    )
    .map_err(bug)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(offset: u32, line: u32, stmt: bool, prologue_end: bool) -> Row {
        Row {
            offset,
            line,
            stmt,
            prologue_end,
        }
    }

    /// Nodes 0 and 1 on line 3, node 2 on none, node 3 on line 4, node 4 on line 3 again.
    fn line_of(node: u32) -> Option<u32> {
        [Some(3), Some(3), None, Some(4), Some(3)]
            .get(node as usize)
            .copied()
            .flatten()
    }

    #[test]
    fn the_prologue_takes_the_first_line_and_a_second_row_ends_it() {
        let rows = rows(&[(8, 12, 0), (12, 20, 1), (20, 30, 3)], line_of);
        assert_eq!(
            rows,
            [
                row(0, 3, true, false),
                row(8, 3, true, true),
                row(20, 4, true, false)
            ]
        );
    }

    #[test]
    fn code_of_no_site_is_line_0_and_starts_no_statement() {
        // Node 2 has no line, so its range is skipped and the gap before node 1's second
        // range is line 0; coming back to line 3 is not a new statement, a change to 4 is.
        let rows = rows(
            &[(0, 4, 0), (4, 6, 2), (6, 10, 1), (12, 14, 4), (14, 16, 3)],
            line_of,
        );
        assert_eq!(
            rows,
            [
                row(0, 3, true, false),
                row(4, 0, false, false),
                row(6, 3, false, false),
                row(10, 0, false, false),
                row(12, 3, false, false),
                row(14, 4, true, false),
            ]
        );
    }

    #[test]
    fn a_function_with_no_line_has_no_rows() {
        assert!(rows(&[(0, 4, 2), (4, 8, 9)], line_of).is_empty());
        assert!(rows(&[], line_of).is_empty());
    }
}

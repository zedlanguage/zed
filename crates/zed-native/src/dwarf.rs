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
//! On x86-64 each name the program binds is a variable of the function whose code uses it, a
//! lambda's parameters its formal parameters (plan row DEBUG-dwarf-clif-bindings, [`bindings`]):
//! one entry per name and function, whose location list gives, over the code where a binding of
//! that name is in scope, that binding's word, a 16-byte `zed_word` of a tag (`enum zed_tag`,
//! [`zed_rt::Word`]'s tags) and its payload, in its stack slot or as a constant; a binding to a
//! non-scalar constant is its value, a string's bytes or another value's printed text
//! ([`ShownTypes`]), as the bytes of its location list. So `print x`
//! shows the binding the source line sees when one name is bound twice in one function. A name
//! bound outside a lambda and read in it is a variable of the body too: the body reads each
//! capture from the closure once, at its start, into a slot of its own frame. `main`'s argument
//! `m` is one variable of `struct MainArgs`, a member for each field the program reads, so
//! `print m` and `print m.args` work though only the fields have words ([`Whole`]).
//!
//! Not yet emitted: columns, and source names for the functions; each subprogram is named by its
//! symbol (`zed_body_3`). No inlined calls are described, since the generator inlines none: each
//! function of the graph is a function of the object, and only primitives are emitted in place.

use std::cmp::Reverse;
use std::collections::BTreeMap;
use std::sync::Arc;

use cranelift_codegen::isa::unwind::UnwindInfo;
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use cranelift_object::object::write::{
    Relocation as ObjectRelocation, SectionId as ObjectSection, StandardSection,
};
use cranelift_object::object::{RelocationEncoding, RelocationFlags, RelocationKind, SectionKind};
use cranelift_object::{ObjectModule, ObjectProduct};
use gimli::write::{
    Address, AttributeValue, CommonInformationEntry, DwarfUnit, EhFrame, EndianVec, Expression,
    FrameTable, LineProgram, LineString, Location, LocationList, Range, RangeList, RelocateWriter,
    Relocation, RelocationTarget, Sections, UnitEntryId,
};
use gimli::{Encoding, Format, LineEncoding, RunTimeEndian};

use zed_kernel::sites::Span;
use zed_rt::Word;
use zedc::source::Lines;

use crate::bug::bug;
use crate::codegen::{Code, Place, Var};

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
/// Each function's bound names ([`Code::vars`]) are its variables, of the type `zed_word`
/// ([`word_type`]), each at the places [`bindings`] gives, the function's frame base its
/// canonical frame address.
///
/// O(T + r log L + f + (r + v) log(r + v)) for a text of T bytes in L lines, r node ranges, f
/// functions and v bound names: the line starts are found once ([`Lines`]), each range's line
/// by binary search, each function's bindings as [`bindings`] says, and each section is
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
    inputs: &[&str],
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
    let word = (code.iter().any(|c| !c.vars.is_empty())).then(|| word_type(&mut dwarf));
    let mut shown_types = ShownTypes::default();
    for (c, name) in code.iter().zip(names) {
        let symbol = symbols.len();
        let at = Address::Symbol { symbol, addend: 0 };
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
        let mut bound = bindings(&c.nodes, &c.vars);
        let wholes = wholes(&mut bound, inputs);
        if let (Some(word), false) = (word, bound.is_empty() && wholes.is_empty()) {
            let mut base = Expression::new();
            base.op(gimli::DW_OP_call_frame_cfa);
            let e = dwarf.unit.get_mut(sub);
            e.set(gimli::DW_AT_frame_base, AttributeValue::Exprloc(base));
            for b in bound {
                // A binding to a non-scalar constant is shown as its value, of its value's type
                // ([`ShownTypes`]); one variable has one type. A name bound to one such value
                // and to no word is one variable whose location list gives the value's bytes
                // (`DW_OP_implicit_value`, DWARF 5 section 2.6.1.1.4) over the code where it is
                // in force, as a word's gives the word.
                let (shown, words): (Vec<_>, Vec<_>) =
                    (b.pieces.iter()).partition(|p| matches!(p.2, Place::Shown(_)));
                let mut blocks: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
                for &&(begin, end, place) in &shown {
                    if let Place::Shown(i) = place {
                        blocks.entry(i).or_default().push((begin, end));
                    }
                }
                if words.is_empty() && blocks.len() == 1 {
                    let (i, pieces) = blocks.pop_first().unwrap();
                    let value = &c.shown[i as usize];
                    let ty = shown_types.of(&mut dwarf, value.string, value.bytes.len());
                    let mut list = vec![Location::BaseAddress { address: at }];
                    list.extend(pieces.iter().map(|&(begin, end)| {
                        let mut x = Expression::new();
                        x.op_implicit_value(value.bytes.clone().into());
                        Location::OffsetPair {
                            begin: u64::from(begin),
                            end: u64::from(end),
                            data: x,
                        }
                    }));
                    let list = dwarf.unit.locations.add(LocationList(list));
                    let v = dwarf.unit.add(sub, gimli::DW_TAG_variable);
                    let e = dwarf.unit.get_mut(v);
                    e.set(
                        gimli::DW_AT_name,
                        AttributeValue::String(b.name.as_bytes().to_vec()),
                    );
                    e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
                    e.set(gimli::DW_AT_location, AttributeValue::LocationListRef(list));
                    continue;
                }
                // A name bound to a word over some of the code and to such a value over other
                // code, or to two such values, has a variable for each value, in a lexical
                // block of the code where it is in force: gdb looks a name up in the innermost
                // block that holds the pc first, as for a C name declared again in an inner
                // block (DWARF 5 section 3.5). Not handled: gdb takes one innermost block, so
                // where two such blocks of different names hold the pc (sibling blocks whose
                // ranges overlap), the name of the block it does not take is not found there.
                // That is how one block per name failed when it was the only form: of `s`,
                // `t` and `u`, all in force at one line, gdb found only `u` (measured, local
                // job dv87, test `gdb_prints_the_value_of_a_name_bound_to_a_constant_that_is_
                // not_a_word`).
                for (i, pieces) in blocks {
                    let ranges = (pieces.iter())
                        .map(|&(begin, end)| Range::StartLength {
                            begin: Address::Symbol {
                                symbol,
                                addend: i64::from(begin),
                            },
                            length: u64::from(end - begin),
                        })
                        .collect();
                    let value = &c.shown[i as usize];
                    let ty = shown_types.of(&mut dwarf, value.string, value.bytes.len());
                    let block = dwarf.unit.add(sub, gimli::DW_TAG_lexical_block);
                    let list = dwarf.unit.ranges.add(RangeList(ranges));
                    let e = dwarf.unit.get_mut(block);
                    e.set(gimli::DW_AT_ranges, AttributeValue::RangeListRef(list));
                    let v = dwarf.unit.add(block, gimli::DW_TAG_variable);
                    let e = dwarf.unit.get_mut(v);
                    e.set(
                        gimli::DW_AT_name,
                        AttributeValue::String(b.name.as_bytes().to_vec()),
                    );
                    e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
                    // A static value (zed/DEBUGGING.md section 4, `DW_AT_const_value`).
                    e.set(
                        gimli::DW_AT_const_value,
                        AttributeValue::Block(value.bytes.clone()),
                    );
                }
                if words.is_empty() {
                    continue;
                }
                let mut list = vec![Location::BaseAddress { address: at }];
                list.extend(
                    words
                        .iter()
                        .map(|&&(begin, end, place)| Location::OffsetPair {
                            begin: u64::from(begin),
                            end: u64::from(end),
                            data: location(place),
                        }),
                );
                let list = dwarf.unit.locations.add(LocationList(list));
                let tag = match b.param {
                    true => gimli::DW_TAG_formal_parameter,
                    false => gimli::DW_TAG_variable,
                };
                let v = dwarf.unit.add(sub, tag);
                let e = dwarf.unit.get_mut(v);
                e.set(
                    gimli::DW_AT_name,
                    AttributeValue::String(b.name.as_bytes().to_vec()),
                );
                e.set(gimli::DW_AT_type, AttributeValue::UnitRef(word));
                e.set(gimli::DW_AT_location, AttributeValue::LocationListRef(list));
            }
            for w in wholes {
                let ty = record_type(&mut dwarf, word, &w.fields);
                let mut list = vec![Location::BaseAddress { address: at }];
                list.extend(w.pieces.iter().map(|(begin, end, places)| {
                    let mut x = Expression::new();
                    for &place in places {
                        if let Some(place) = place {
                            put_location(&mut x, place);
                        }
                        x.op_piece(WORD_BYTES);
                    }
                    Location::OffsetPair {
                        begin: u64::from(*begin),
                        end: u64::from(*end),
                        data: x,
                    }
                }));
                let list = dwarf.unit.locations.add(LocationList(list));
                let tag = match w.param {
                    true => gimli::DW_TAG_formal_parameter,
                    false => gimli::DW_TAG_variable,
                };
                let v = dwarf.unit.add(sub, tag);
                let e = dwarf.unit.get_mut(v);
                e.set(
                    gimli::DW_AT_name,
                    AttributeValue::String(w.name.as_bytes().to_vec()),
                );
                e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
                e.set(gimli::DW_AT_location, AttributeValue::LocationListRef(list));
            }
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

/// Adds the type of a word ([`Word`]) to `dwarf`, and returns it: `struct zed_word` of 16
/// bytes, its `tag` at offset 0, an `enum zed_tag` of 8 bytes whose enumerators are the tag
/// constants by their names, and its payload `bits` at offset 8, an `i64`. So gdb prints a
/// binding as `{tag = INT, bits = 5}`. The payload is not described as a variant part on the
/// tag (DWARF 5 section 5.7.10): what a cell's or a value's index stands for is in the
/// runtime's tables, which the DWARF cannot reach.
fn word_type(dwarf: &mut DwarfUnit) -> UnitEntryId {
    let root = dwarf.unit.root();
    let int = dwarf.unit.add(root, gimli::DW_TAG_base_type);
    let e = dwarf.unit.get_mut(int);
    e.set(gimli::DW_AT_name, AttributeValue::String("i64".into()));
    e.set(
        gimli::DW_AT_encoding,
        AttributeValue::Encoding(gimli::DW_ATE_signed),
    );
    e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(8));
    let tag = dwarf.unit.add(root, gimli::DW_TAG_enumeration_type);
    let e = dwarf.unit.get_mut(tag);
    e.set(gimli::DW_AT_name, AttributeValue::String("zed_tag".into()));
    e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(8));
    e.set(gimli::DW_AT_type, AttributeValue::UnitRef(int));
    for (name, value) in [
        ("INT", Word::INT),
        ("FLOAT", Word::FLOAT),
        ("BOOL", Word::BOOL),
        ("CELL", Word::CELL),
        ("VAL", Word::VAL),
        ("PRIM", Word::PRIM),
        ("SOURCE", Word::SOURCE),
        ("STATE", Word::STATE),
        ("ERR", Word::ERR),
    ] {
        let k = dwarf.unit.add(tag, gimli::DW_TAG_enumerator);
        let e = dwarf.unit.get_mut(k);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.into()));
        e.set(gimli::DW_AT_const_value, AttributeValue::Sdata(value));
    }
    let word = dwarf.unit.add(root, gimli::DW_TAG_structure_type);
    let e = dwarf.unit.get_mut(word);
    e.set(gimli::DW_AT_name, AttributeValue::String("zed_word".into()));
    e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(WORD_BYTES));
    for (name, ty, at) in [("tag", tag, 0), ("bits", int, 8)] {
        let m = dwarf.unit.add(word, gimli::DW_TAG_member);
        let e = dwarf.unit.get_mut(m);
        e.set(gimli::DW_AT_name, AttributeValue::String(name.into()));
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
        e.set(gimli::DW_AT_data_member_location, AttributeValue::Udata(at));
    }
    word
}

/// The bytes of a [`Word`], a tag and a payload of 8 bytes each.
const WORD_BYTES: u64 = 16;

/// Adds the type of a [`Whole`] with `fields` to `dwarf`, and returns it: `struct MainArgs`,
/// a `zed_word` member per field read, in order, one word apart. A field the program does not
/// read is not a member, since no word of it exists.
fn record_type(dwarf: &mut DwarfUnit, word: UnitEntryId, fields: &[Arc<str>]) -> UnitEntryId {
    let root = dwarf.unit.root();
    let t = dwarf.unit.add(root, gimli::DW_TAG_structure_type);
    let e = dwarf.unit.get_mut(t);
    e.set(gimli::DW_AT_name, AttributeValue::String("MainArgs".into()));
    let size = WORD_BYTES * fields.len() as u64;
    e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(size));
    for (i, f) in fields.iter().enumerate() {
        let m = dwarf.unit.add(t, gimli::DW_TAG_member);
        let e = dwarf.unit.get_mut(m);
        e.set(
            gimli::DW_AT_name,
            AttributeValue::String(f.as_bytes().to_vec()),
        );
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(word));
        let at = WORD_BYTES * i as u64;
        e.set(gimli::DW_AT_data_member_location, AttributeValue::Udata(at));
    }
    t
}

/// The location of a word at `place` ([`put_location`]).
fn location(place: Place) -> Expression {
    let mut x = Expression::new();
    put_location(&mut x, place);
    x
}

/// Appends to `x` the location of a word at `place`: in the frame, at its offset from the frame
/// base, the canonical frame address (`DW_OP_fbreg`); a constant, its 16 bytes
/// (`DW_OP_implicit_value`), little end first, as on x86-64, the one target [`Code::vars`] is
/// given for.
fn put_location(x: &mut Expression, place: Place) {
    match place {
        Place::Frame(offset) => x.op_fbreg(offset),
        Place::Word(w) => {
            // A constant is an implicit location description, the value itself (DWARF 5,
            // section 2.6.1.1.4, `DW_OP_implicit_value`), one entry of the binding's location
            // list. Not `DW_AT_const_value` on the variable: that gives one value over the
            // whole scope with no location (section 4.1), and a name bound to a constant over
            // some of the code and to a frame slot over the rest needs one list for both.
            let mut bytes = Vec::with_capacity(16);
            bytes.extend(w.tag.to_le_bytes());
            bytes.extend(w.bits.to_le_bytes());
            x.op_implicit_value(bytes.into());
        }
        // No word: [`add`] writes such a binding as a variable of its own, and a field of
        // `main`'s argument ([`Whole`]) is an input, never a constant. An empty location is
        // one gdb shows as `<optimized out>`.
        Place::Shown(_) => {}
    }
}

/// The types of the [`Shown`](crate::codegen::Shown) constants of one compilation unit, each
/// added once: `zed_str`, for a string's bytes, and `zed_text`, for another value's printed
/// text, each a name (`DW_TAG_typedef`) for an array of its length in `char`s
/// (`DW_TAG_array_type` with a `DW_TAG_subrange_type` of that `DW_AT_count`, DWARF 5 sections
/// 5.5 and 5.13), which gdb prints as a string, `"hi"`. O(log t) a lookup for t types.
#[derive(Default)]
struct ShownTypes {
    byte: Option<UnitEntryId>,
    of: BTreeMap<(bool, usize), UnitEntryId>,
}

impl ShownTypes {
    /// The type of a [`Shown`](crate::codegen::Shown) of `len` bytes, a string's when `string`.
    fn of(&mut self, dwarf: &mut DwarfUnit, string: bool, len: usize) -> UnitEntryId {
        if let Some(&t) = self.of.get(&(string, len)) {
            return t;
        }
        let root = dwarf.unit.root();
        let byte = *self.byte.get_or_insert_with(|| {
            let t = dwarf.unit.add(root, gimli::DW_TAG_base_type);
            let e = dwarf.unit.get_mut(t);
            e.set(gimli::DW_AT_name, AttributeValue::String("char".into()));
            e.set(
                gimli::DW_AT_encoding,
                AttributeValue::Encoding(gimli::DW_ATE_signed_char),
            );
            e.set(gimli::DW_AT_byte_size, AttributeValue::Udata(1));
            t
        });
        let array = dwarf.unit.add(root, gimli::DW_TAG_array_type);
        dwarf
            .unit
            .get_mut(array)
            .set(gimli::DW_AT_type, AttributeValue::UnitRef(byte));
        let range = dwarf.unit.add(array, gimli::DW_TAG_subrange_type);
        dwarf
            .unit
            .get_mut(range)
            .set(gimli::DW_AT_count, AttributeValue::Udata(len as u64));
        let t = dwarf.unit.add(root, gimli::DW_TAG_typedef);
        let e = dwarf.unit.get_mut(t);
        let name = if string { "zed_str" } else { "zed_text" };
        e.set(gimli::DW_AT_name, AttributeValue::String(name.into()));
        e.set(gimli::DW_AT_type, AttributeValue::UnitRef(array));
        self.of.insert((string, len), t);
        t
    }
}

/// One name bound in a function, as its DWARF variable: whether a binding of it is a parameter
/// of the function, and where its word is over the code, as `(begin, end, place)`, offsets from
/// the function's start, sorted and disjoint.
#[derive(Debug, PartialEq)]
pub(crate) struct Binding {
    pub name: Arc<str>,
    pub param: bool,
    pub pieces: Vec<(u32, u32, Place)>,
}

/// The names bound in a function whose node ranges are `nodes` (as [`Code::nodes`]) and whose
/// bindings are `vars`, one [`Binding`] per name, in the order the names are first bound;
/// a name with no code in its scopes is left out.
///
/// One name may be bound twice in a function, in an inner region or again in the same region,
/// and gdb shows one variable of a name, so the bindings of a name are merged into one list:
/// where scopes overlap, the binding whose scope starts later, the inner or the later one, is
/// the one in force, as in the source. A sweep over the scopes sorted by start (and the longer
/// first at one start) keeps a stack of the scopes open, each with the first node number it
/// still holds: a scope that starts ends the piece of the one on top before it, and the ones
/// it outlasts; a scope that ends gives the rest to the one under it. Each piece of numbers
/// `[a, e]` is then the code of the nodes numbered `a` to `e` ([`Runs`]): each run of ranges
/// of those nodes with no range of another node between them, and the code of no node
/// between them. Cranelift may move a node's code in among another's, and the code of a node
/// outside the piece is left out, so there gdb says the name is not available rather than
/// show the word of a binding the source line does not see. Pieces of one name are disjoint
/// in numbers, so their code is disjoint; two that touch in the code with one place are
/// joined.
///
/// Why the word is in its place over that code: a binding's word is stored by its node, or at
/// its region's entry for an argument, and its scope starts after that store (`Gen::finish`,
/// `Gen::bind_args`), in the same region or one the store dominates. Cranelift keeps the order
/// of the instructions with side effects, the stores among them, and places each pure one just
/// before the first instruction that needs it (cranelift-codegen 0.137.1
/// `egraph/elaborate.rs`:150 and :497), except that it hoists code out of a loop (:659). At
/// the default `opt_level` `none` that pass does not run at all (`Context::optimize`). The
/// code built here has no loops: `Gen::function` checks it, and records no names for a
/// function with one. So code marked with a node in the scope runs after the store, and a slot
/// is stored once (`Gen::put` takes a new one each time).
///
/// O((r + v) log(r + v) + p log p) for r ranges, v bindings and p pieces written: the
/// bindings sorted, and each pushed and popped once, making at most two pieces of numbers;
/// each of those found in [`Runs`] in O(log r) and O(log k) more per run of the k it makes.
/// The p pieces are what the location lists hold, so no method writes them in less.
pub(crate) fn bindings(nodes: &[(u32, u32, u32)], vars: &[Var]) -> Vec<Binding> {
    if vars.is_empty() {
        return Vec::new();
    }
    let runs = Runs::new(nodes);
    // The bindings of each name, in the order each name is first bound.
    let mut groups: Vec<(Arc<str>, Vec<usize>)> = Vec::new();
    let mut of: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, v) in vars.iter().enumerate() {
        let g = *of.entry(&v.name).or_insert_with(|| {
            groups.push((v.name.clone(), Vec::new()));
            groups.len() - 1
        });
        groups[g].1.push(i);
    }
    let scope = |i: usize| (u64::from(vars[i].scope.0), u64::from(vars[i].scope.1));
    let mut out = Vec::with_capacity(groups.len());
    for (name, mut ix) in groups {
        ix.sort_by_key(|&i| (scope(i).0, Reverse(scope(i).1), i));
        let mut pieces = Vec::new();
        let mut piece = |i: usize, a: u64, e: u64| {
            if a <= e {
                for (begin, end) in runs.of(a, e) {
                    pieces.push((begin, end, vars[i].place));
                }
            }
        };
        // Each open scope, and the first number it still holds.
        let mut open: Vec<(usize, u64)> = Vec::new();
        for &s in &ix {
            let (a, e) = scope(s);
            while let Some(&(t, from)) = open.last() {
                if scope(t).1 >= a {
                    break;
                }
                open.pop();
                piece(t, from, scope(t).1);
            }
            if let (Some(&(t, from)), Some(before)) = (open.last(), a.checked_sub(1)) {
                piece(t, from, before);
            }
            while open.last().is_some_and(|&(t, _)| scope(t).1 <= e) {
                open.pop();
            }
            if let Some(top) = open.last_mut() {
                top.1 = e + 1;
            }
            open.push((s, a));
        }
        while let Some((t, from)) = open.pop() {
            piece(t, from, scope(t).1);
        }
        pieces.sort_unstable_by_key(|p| p.0);
        pieces.dedup_by(|next, last| {
            let joined = last.1 == next.0 && last.2 == next.2;
            if joined {
                last.1 = next.1;
            }
            joined
        });
        if !pieces.is_empty() {
            let param = ix.iter().any(|&i| vars[i].param);
            out.push(Binding {
                name,
                param,
                pieces,
            });
        }
    }
    out
}

/// A record the program reads field by field, as one DWARF variable of a structure type with a
/// member for each field read: `main`'s argument `m`, of type `MainArgs`. The program reads
/// `m.args`, and the syntax builder makes each such read one name, `m.args`
/// (`zedc-syntax` `ast/builder.rs`, `Builder::main_use`), so no word of the whole `m` exists:
/// gdb's `print m` and `print m.args` read this variable, whose location over each piece of
/// code is the fields' words one after another (`DW_OP_piece`, DWARF 5 section 2.6.1.2), a
/// field not available there an empty piece, which gdb shows as `<optimized out>`.
#[derive(Debug, PartialEq)]
pub(crate) struct Whole {
    pub name: Arc<str>,
    pub param: bool,
    /// The fields read, in the order first bound.
    pub fields: Vec<Arc<str>>,
    /// Over the code, as `(begin, end, places)`, sorted and disjoint: `places[i]` is the word
    /// of `fields[i]` there, if available.
    pub pieces: Vec<(u32, u32, Vec<Option<Place>>)>,
}

/// Takes the bindings of `main`'s inputs `inputs` named `p.f` out of `bound` and gives one
/// [`Whole`] `p` for each `p`, in the order its first field is bound; `bound` keeps the others in
/// their order. `inputs` are the names of `main`'s parameters (`zedc::run::Ports::inputs`),
/// which `Builder::main_header` (`zedc-syntax` `ast/stmts.rs`) makes `p.f` for each field `f`
/// of `MainArgs` the body reads, and `main::files` or a bare `f` in a `main` with no
/// parameter, which have no dot and are left as they are. A name is grouped by being one of
/// them, not by its dot: another binding may have a dot, a method `Point.norm`
/// (`zedc-resolve` `resolve.rs`, `StmtKind::Method`), and is not a field of anything here. A
/// `p` also bound as a name of its own keeps its fields as they are, so no two variables of
/// one name are written.
///
/// The k fields' pieces are cut at every begin and end of a piece of any of them, and each
/// interval between two cuts takes the place of each field's piece over it, found by a cursor
/// per field that only moves forward; touching intervals of the same places are joined.
/// O(p log p + p k) for p pieces: the cuts sorted, and each interval looked at once per field.
/// The inputs with a dot are `args`, `stdin` and `env` (`MAIN_INPUTS`), so k ≤ 3, and the
/// test of a name against `inputs` is O(1).
pub(crate) fn wholes(bound: &mut Vec<Binding>, inputs: &[&str]) -> Vec<Whole> {
    let plain: std::collections::BTreeSet<Arc<str>> = (bound.iter())
        .filter(|b| !b.name.contains('.'))
        .map(|b| b.name.clone())
        .collect();
    let mut kept = Vec::with_capacity(bound.len());
    // The fields of each whole, as (whole's name, field's name, its binding).
    type Fields = Vec<(Arc<str>, Binding)>;
    let mut groups: Vec<(Arc<str>, Fields)> = Vec::new();
    let mut of: BTreeMap<Arc<str>, usize> = BTreeMap::new();
    for b in bound.drain(..) {
        let field = (b.name.split_once('.'))
            .filter(|(p, _)| inputs.contains(&&*b.name) && !plain.contains(*p));
        let Some((p, f)) = field else {
            kept.push(b);
            continue;
        };
        let (p, f): (Arc<str>, Arc<str>) = (p.into(), f.into());
        let g = *of.entry(p.clone()).or_insert_with(|| {
            groups.push((p, Vec::new()));
            groups.len() - 1
        });
        groups[g].1.push((f, b));
    }
    *bound = kept;
    let mut out = Vec::with_capacity(groups.len());
    for (name, fields) in groups {
        let mut cuts: Vec<u32> = (fields.iter())
            .flat_map(|(_, b)| b.pieces.iter().flat_map(|p| [p.0, p.1]))
            .collect();
        cuts.sort_unstable();
        cuts.dedup();
        let mut at = vec![0; fields.len()];
        let mut pieces: Vec<(u32, u32, Vec<Option<Place>>)> = Vec::new();
        for w in cuts.windows(2) {
            let (x, y) = (w[0], w[1]);
            // A piece of a field that starts at or before `x` ends at or after `y`: its end
            // is a cut, and no cut is between `x` and `y`.
            let places: Vec<Option<Place>> = (fields.iter().zip(&mut at))
                .map(|((_, b), i)| {
                    while b.pieces.get(*i).is_some_and(|p| p.1 <= x) {
                        *i += 1;
                    }
                    b.pieces.get(*i).filter(|p| p.0 <= x).map(|p| p.2)
                })
                .collect();
            if places.iter().all(Option::is_none) {
                continue;
            }
            match pieces.last_mut() {
                Some(last) if last.1 == x && last.2 == places => last.1 = y,
                _ => pieces.push((x, y, places)),
            }
        }
        out.push(Whole {
            name,
            param: fields.iter().any(|(_, b)| b.param),
            fields: fields.iter().map(|(f, _)| f.clone()).collect(),
            pieces,
        });
    }
    out
}

/// The code of the nodes numbered `a` to `e`, as runs of their ranges that follow one another
/// in the code with no range of another node between them, each run with the code of no node
/// between its ranges (see [`bindings`]).
///
/// In code order, range j starts a run of `[a, e]` when its number is in `[a, e]` and the
/// range before it is missing or has a number outside: below `a` or above `e`. Over the
/// ranges sorted by number, those with a number in `[a, e]` are an interval, found by two
/// binary searches, and the starts among them are the ones whose key, the number of the range
/// before (-1 when there is none), is below `a`, and those whose key is above `e`: two
/// three-sided queries, each answered by a sparse table of the least key over each run of 2^k
/// (Bender and Farach-Colton, "The LCA Problem Revisited", LATIN 2000, section 3), the second
/// over the negated keys: the least key of the interval, if below the bound, is an answer, and
/// the two sides of it are searched the same way, so a query that finds k costs O(1 + k)
/// lookups. The ends are found the same way from the range after. The two queries are
/// disjoint, and the i-th start in code order and the i-th end make the i-th run, since runs
/// do not nest. O(r log r) to build for r ranges, O(log r + k log k) for a query of k runs.
///
/// Why a run spans the code of no node between its ranges. Every instruction of the CLIF
/// carries a node's number (`Gen::walk`), so the code of no node is Cranelift's own
/// (cranelift-codegen 0.137.1, read 2026-11-26): the prologue (`machinst/vcode.rs`:863),
/// which comes before every range; the padding before a block and the jump around a constant
/// island, which do not run or only jump; and code at the start or the end of a block, where
/// no instruction's location is current (`end_srcloc` at :1089): the register allocator's
/// moves on entry to a block, and a block split from a critical edge, a jump and its moves
/// (`machinst/lower.rs`:1304, under the default location), which `blockorder.rs`:206–229
/// places right after the block the edge leaves; cold blocks go last (`vcode.rs`:759), and
/// the only cold blocks here are the error exits (`Gen::exit`), which have one predecessor
/// each, so no edge into them is split. Code of no node between two ranges of the run is
/// therefore the end of the block of the range before, run after it, or the start of the
/// block of the range after, whose first code is in the scope; both run after the word is
/// stored, as [`bindings`] argues for the code of the scope's nodes. Splitting a run there,
/// as an earlier version did, cut each scope at every block after its start, which made the
/// pieces quadratic in the program: 176,499 for 100 reads of files, 41,208 for a chain of 200
/// joins (job dv50, 2026-11-26), where gdb needs no more than one per scope.
///
/// The number of runs. A range j starts a run of `[a, e]` when `n_j` is in it and `n_{j-1}`
/// is not, writing `n_j` for the number of the j-th range in code order and `n_0 = -1` for
/// the range before the first, which adds no descent. If `n_{j-1} < n_j`,
/// that is `n_{j-1} < a ≤ n_j`: the sequence crosses the level `a - 1/2` upward at j. If
/// `n_{j-1} > n_j`, it is `n_j ≤ e < n_{j-1}`: it crosses `e + 1/2` downward. A sequence of
/// r numbers with d descents (`n_{j-1} > n_j`) crosses any level downward at most d times,
/// since each crossing is a descent, and upward at most d + 1 times, since two upward
/// crossings have a downward one between them. So a piece of numbers has at most 2d + 1 runs,
/// and the p pieces of [`bindings`] at most (2d + 1) p, with p ≤ 2v for v bindings.
///
/// No list that shows a name only over its scope's code has fewer: between two runs of a
/// scope lies the code of a node outside it, so each run is a piece of its own. The count
/// therefore depends on d whatever method builds the lists, and a layout against node order
/// makes it Θ(v r): numbers 1, k + 1, 2, k + 2, … and v names over `[1, k]` give each name k
/// runs (test `a_layout_against_node_order_has_a_piece_for_each_run_of_each_scope`). A bound
/// in v + r alone is not possible.
///
/// A `DW_TAG_lexical_block` per scope, whose `DW_AT_ranges` hold the runs once for every name
/// declared in it, with each name's list over the hull of its scope, changes the constant
/// only. It does help in the layout above: the v names share the scope `[1, k]`, so its k runs
/// are written once and each list has one entry, k + v in all. But no two bindings here share
/// a scope: each scope starts after its own store (`Gen::finish`), so those of one region are
/// `[a_1, E] ⊃ [a_2, E] ⊃ …`, and each name's list must still leave out the region's code of
/// nodes before its store wherever that code lies after it. Take one region of nodes 1 to k,
/// `x_i` stored at node i with scope `[i + 1, k]`, and code in the order 1, k, 2, k - 1, 3, …:
/// in the hull of `x_i`'s scope the nodes 2 to i lie between code of the scope, so its list
/// has about i entries, Θ(k²) = Θ(v r) in all; a block per binding lists its own runs, the
/// same count, and DWARF can neither subtract ranges nor share part of a list. Blocks per
/// region would roughly halve the entries when the descents come from code of other regions
/// (plan row DEBUG-dwarf-lexical-blocks). That d stays small is measured, not proved: the code
/// built here is in node order but for the error exits after it, and the test
/// `the_pieces_of_the_names_grow_linearly_with_the_program` (lib.rs) fails if the largest d
/// of a function grows from n to 8n or the pieces grow more than 9 times.
struct Runs {
    /// The ranges in code order, as `(start, end)`.
    code: Vec<(u32, u32)>,
    /// The ranges' numbers, sorted, and the index in `code` of each.
    numbers: Vec<u32>,
    at: Vec<usize>,
    /// Over the ranges sorted by number, the key of the range before in the code and its
    /// negation, then of the range after.
    before: (Least, Least),
    after: (Least, Least),
}

impl Runs {
    fn new(nodes: &[(u32, u32, u32)]) -> Runs {
        let mut code: Vec<(u32, u32, u32)> = nodes.iter().copied().filter(|r| r.0 < r.1).collect();
        code.sort_unstable();
        let mut order: Vec<usize> = (0..code.len()).collect();
        order.sort_unstable_by_key(|&j| (code[j].2, j));
        let key_before = |j: usize| j.checked_sub(1).map_or(-1, |p| i64::from(code[p].2));
        let key_after = |j: usize| code.get(j + 1).map_or(-1, |r| i64::from(r.2));
        let tables = |key: &dyn Fn(usize) -> i64| {
            let keys: Vec<i64> = order.iter().map(|&j| key(j)).collect();
            let negated = keys.iter().map(|k| -k).collect();
            (Least::new(keys), Least::new(negated))
        };
        Runs {
            before: tables(&key_before),
            after: tables(&key_after),
            numbers: order.iter().map(|&j| code[j].2).collect(),
            at: order,
            code: code.into_iter().map(|r| (r.0, r.1)).collect(),
        }
    }

    fn of(&self, a: u64, e: u64) -> Vec<(u32, u32)> {
        let lo = self.numbers.partition_point(|&k| u64::from(k) < a);
        let hi = self.numbers.partition_point(|&k| u64::from(k) <= e);
        if lo >= hi {
            return Vec::new();
        }
        // Keys are u32 numbers or -1, so a bound past u32::MAX acts as u32::MAX + 1 does.
        let (a, e) = (a.min(1 << 33) as i64, e.min(1 << 33) as i64);
        let side = |(least, most): &(Least, Least)| {
            let mut out = Vec::new();
            least.below(lo, hi, a, &mut out);
            most.below(lo, hi, -e, &mut out);
            let mut out: Vec<usize> = out.into_iter().map(|i| self.at[i]).collect();
            out.sort_unstable();
            out
        };
        let (starts, ends) = (side(&self.before), side(&self.after));
        (starts.iter().zip(&ends))
            .map(|(&s, &t)| (self.code[s].0, self.code[t].1))
            .collect()
    }
}

/// A sparse table of the least of `keys` over each run of 2^k of them, for the three-sided
/// queries of [`Runs`].
struct Least {
    keys: Vec<i64>,
    /// Level k: the index of the least key of the 2^k from each one.
    levels: Vec<Vec<usize>>,
}

impl Least {
    fn new(keys: Vec<i64>) -> Least {
        let mut levels = vec![(0..keys.len()).collect::<Vec<_>>()];
        let mut w = 1;
        while 2 * w <= keys.len() {
            let last = &levels[levels.len() - 1];
            let next = (0..=keys.len() - 2 * w)
                .map(|i| {
                    let (x, y) = (last[i], last[i + w]);
                    if keys[y] < keys[x] { y } else { x }
                })
                .collect();
            levels.push(next);
            w *= 2;
        }
        Least { keys, levels }
    }

    /// The index of the least key in `lo..hi`, which is not empty.
    fn least(&self, lo: usize, hi: usize) -> usize {
        let k = (hi - lo).ilog2() as usize;
        let (x, y) = (self.levels[k][lo], self.levels[k][hi - (1 << k)]);
        if self.keys[y] < self.keys[x] { y } else { x }
    }

    /// Adds to `out` each index in `lo..hi` whose key is below `bound`, in O(1 + k) lookups
    /// for the k it adds: the least key of a part is the only one to look at, and a part whose
    /// least is not below the bound has none.
    fn below(&self, lo: usize, hi: usize, bound: i64, out: &mut Vec<usize>) {
        let mut todo = vec![(lo, hi)];
        while let Some((lo, hi)) = todo.pop() {
            if lo >= hi {
                continue;
            }
            let m = self.least(lo, hi);
            if self.keys[m] < bound {
                out.push(m);
                todo.extend([(lo, m), (m + 1, hi)]);
            }
        }
    }
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

    /// Nodes 1 to 10, node n's code at offsets 10n to 10n + 10.
    fn in_order() -> Vec<(u32, u32, u32)> {
        (1..=10).map(|n| (10 * n, 10 * n + 10, n)).collect()
    }

    fn var(name: &str, at: i64, scope: (u32, u32)) -> Var {
        Var {
            name: name.into(),
            place: Place::Frame(at),
            scope,
            param: false,
        }
    }

    /// Each binding's name and its pieces, `(begin, end, place)`.
    type Pieces<'a> = Vec<(&'a str, Vec<(u32, u32, Place)>)>;

    fn pieces(b: &[Binding]) -> Pieces<'_> {
        b.iter().map(|b| (&*b.name, b.pieces.clone())).collect()
    }

    #[test]
    fn a_name_bound_again_in_its_region_is_the_later_binding_from_there() {
        let b = bindings(
            &in_order(),
            &[var("x", -16, (2, 10)), var("x", -32, (5, 10))],
        );
        let (a, c) = (Place::Frame(-16), Place::Frame(-32));
        assert_eq!(pieces(&b), [("x", vec![(20, 50, a), (50, 110, c)])]);
    }

    #[test]
    fn a_name_bound_in_an_inner_region_is_the_inner_binding_there_only() {
        let b = bindings(
            &in_order(),
            &[var("x", -16, (1, 10)), var("x", -32, (4, 6))],
        );
        let (a, c) = (Place::Frame(-16), Place::Frame(-32));
        assert_eq!(
            pieces(&b),
            [("x", vec![(10, 40, a), (40, 70, c), (70, 110, a)])]
        );
    }

    #[test]
    fn a_name_with_no_code_in_its_scope_is_left_out_and_a_parameter_is_one() {
        let w = Word {
            tag: Word::INT,
            bits: 9,
        };
        let z = Var {
            name: "z".into(),
            place: Place::Word(w),
            scope: (3, 4),
            param: true,
        };
        let b = bindings(
            &in_order(),
            &[var("x", -16, (1, 1)), var("y", -32, (11, 12)), z],
        );
        assert_eq!(
            pieces(&b),
            [
                ("x", vec![(10, 20, Place::Frame(-16))]),
                ("z", vec![(30, 50, Place::Word(w))])
            ]
        );
        assert_eq!(b.iter().map(|b| b.param).collect::<Vec<_>>(), [false, true]);
        assert!(bindings(&in_order(), &[]).is_empty());
        assert!(bindings(&[], &[var("x", -16, (0, 3))]).is_empty());
    }

    #[test]
    fn the_pieces_of_one_place_on_both_sides_of_an_inner_binding_with_no_code_are_one() {
        let nodes = [(10, 20, 1), (20, 30, 2), (30, 30, 3), (30, 40, 4)];
        let b = bindings(&nodes, &[var("x", -16, (1, 4)), var("x", -32, (3, 3))]);
        assert_eq!(pieces(&b), [("x", vec![(10, 40, Place::Frame(-16))])]);
    }

    #[test]
    fn a_layout_against_node_order_has_a_piece_for_each_run_of_each_scope() {
        // Code in the order 1, k + 1, 2, k + 2, …: d = k - 1 descents, and each of v names
        // over [1, k] has k runs, one piece each, and one name over [k + 1, 2k] has k too.
        let (k, v) = (32u32, 8);
        let nodes: Vec<(u32, u32, u32)> = (0..2 * k)
            .map(|j| {
                (
                    10 * j,
                    10 * j + 10,
                    if j % 2 == 0 { j / 2 + 1 } else { k + j / 2 + 1 },
                )
            })
            .collect();
        let mut vars: Vec<Var> = (0..v).map(|i| var(&format!("x{i}"), -16, (1, k))).collect();
        vars.push(var("y", -32, (k + 1, 2 * k)));
        let b = bindings(&nodes, &vars);
        let d = nodes.windows(2).filter(|w| w[0].2 > w[1].2).count();
        assert_eq!(d, k as usize - 1);
        for (i, x) in b.iter().enumerate() {
            let odd = u32::from(x.name.as_ref() == "y");
            let want: Vec<(u32, u32, Place)> = (0..k)
                .map(|j| (20 * j + 10 * odd, 20 * j + 10 * odd + 10, x.pieces[0].2))
                .collect();
            assert_eq!(x.pieces, want, "{i}");
        }
        let total: usize = b.iter().map(|b| b.pieces.len()).sum();
        assert_eq!(total, (v + 1) * k as usize);
        assert!(total <= (2 * d + 1) * 2 * vars.len());
    }

    #[test]
    fn the_fields_of_main_s_argument_are_one_variable_of_their_pieces() {
        // `m.args` over nodes 1 to 4 and `m.env` over 3 to 6 make `m`, with `m.env` not
        // available over 1 and 2 and `m.args` not over 5 and 6; `x` stays as it is, and so do
        // `y.args` and `y`, since `y` is also bound as a name of its own, and the method
        // `Point.norm`, which is not one of `main`'s inputs, though its name has a dot.
        let (a, e) = (Place::Frame(-16), Place::Frame(-32));
        let mut b = bindings(
            &in_order(),
            &[
                var("x", -48, (1, 10)),
                var("m.args", -16, (1, 4)),
                var("y.args", -64, (1, 2)),
                var("Point.norm", -96, (1, 10)),
                var("m.env", -32, (3, 6)),
                var("y", -80, (1, 2)),
            ],
        );
        let w = wholes(&mut b, &["m.args", "m.env", "y.args"]);
        let names: Vec<&str> = b.iter().map(|b| &*b.name).collect();
        assert_eq!(names, ["x", "y.args", "Point.norm", "y"]);
        let fields: Vec<&str> = w[0].fields.iter().map(|f| &**f).collect();
        assert_eq!(
            (w.len(), &*w[0].name, fields),
            (1, "m", vec!["args", "env"])
        );
        assert_eq!(
            w[0].pieces,
            [
                (10, 30, vec![Some(a), None]),
                (30, 50, vec![Some(a), Some(e)]),
                (50, 70, vec![None, Some(e)]),
            ]
        );
        assert!(!w[0].param);
    }

    #[test]
    fn code_moved_in_among_a_binding_shows_the_binding_its_node_sees_or_none() {
        // Cranelift moved node 3's code in among nodes 1 and 2, and node 5's between 2 and 4,
        // with a gap of code of no node at 50 to 60, which the run of node 4 spans. x is one
        // binding over nodes 1 and 2 and another over 3 and 4; y is bound over 1 and 2 only,
        // so not at node 3's code.
        let nodes = [
            (0, 10, 1),
            (10, 20, 3),
            (20, 30, 2),
            (30, 40, 5),
            (40, 50, 4),
            (60, 70, 4),
        ];
        let vars = [
            var("x", -16, (1, 2)),
            var("x", -32, (3, 4)),
            var("y", -48, (1, 2)),
        ];
        let b = bindings(&nodes, &vars);
        let (a, c, y) = (Place::Frame(-16), Place::Frame(-32), Place::Frame(-48));
        assert_eq!(
            pieces(&b),
            [
                ("x", vec![(0, 10, a), (10, 20, c), (20, 30, a), (40, 70, c)]),
                ("y", vec![(0, 10, y), (20, 30, y)])
            ]
        );
    }

    #[test]
    fn the_runs_of_numbers_are_the_ranges_of_those_numbers_with_no_other_between() {
        // Every interval of numbers against a plain walk of the ranges in code order, over
        // code out of node order, with gaps in the numbers and in the code, which a run spans,
        // and a number with two ranges.
        let mut nodes: Vec<(u32, u32, u32)> = (0..37u32)
            .map(|i| {
                let s = (i * 17) % 37 * 8;
                (s, s + 4 + 4 * u32::from(i % 3 != 0), 2 * (i % 31) + i % 2)
            })
            .collect();
        nodes.push((400, 400, 5));
        let runs = Runs::new(&nodes);
        let mut code = nodes.clone();
        code.retain(|r| r.0 < r.1);
        code.sort_unstable();
        for a in 0..70u64 {
            for e in a..70u64 {
                let mut want: Vec<(u32, u32)> = Vec::new();
                let mut open = false;
                for r in &code {
                    let inside = (a..=e).contains(&u64::from(r.2));
                    match want.last_mut() {
                        Some(last) if inside && open => last.1 = r.1,
                        _ if inside => want.push((r.0, r.1)),
                        _ => {}
                    }
                    open = inside;
                }
                assert_eq!(runs.of(a, e), want, "{a} {e}");
            }
        }
        assert!(Runs::new(&[]).of(0, 9).is_empty());
    }
}

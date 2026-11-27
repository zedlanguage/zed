//! The DWARF of an executable (plan row DEBUG-dwarf-clif, zed/DEBUGGING.md sections 4 to 6):
//! the object file's code is the same with and without its debug sections, and gdb, run in
//! batch mode on an executable `zedc build` makes, stops at a function and at source lines,
//! walks the stack to the C `main`, steps through a function's lines in source order,
//! evaluates an expression, prints the thread-local `zed_debug_task` and `zed_debug_keypath`,
//! and stops at a breakpoint conditioned on the task only when its condition holds, on each
//! step program and enabled corpus program; an executable whose line table is removed fails
//! that check (the negative control).
//!
//! gdb prints the words the program's names are bound to, in the frame and constants, as the
//! type `zed_word` of a tag and a payload (plan row DEBUG-dwarf-clif-bindings). No inlined
//! calls are described, since the generator inlines none.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use object::{Object as _, ObjectSection as _, ObjectSymbol as _, RelocationTarget, SymbolKind};
use zed_tests::oracle::{self, ENABLED};
use zedc::zir::lower::lower_debug;

use super::{built, dir};

/// A program whose `main` has one statement on each of lines 2 to 6, each read from the
/// command line so that none is worked out while the program is compiled.
const CHAIN: &str = "main(m: MainArgs) {
    s0 = String(m.args);
    s1 = s0 ++ \"x\";
    s2 = s1 ++ \"y\";
    s3 = s2 ++ \"z\";
    m.stdout <- s3;
}
";

/// The program `src`, written to the file `name.zed` of test `name`, and its path.
fn written(name: &str, src: &str) -> PathBuf {
    let file = dir(&format!("dwarf/{name}")).join(format!("{name}.zed"));
    std::fs::write(&file, src).unwrap();
    file
}

/// The object file `zedc build` makes for the program in `file`, with its debug sections when
/// `debug`.
fn object_file(file: &Path, debug: bool) -> Vec<u8> {
    object_of(&loaded(file, zedc::run::load_file_named), debug)
}

/// The program in `file`, loaded by `load`, [`zedc::run::load_file`] or `load_file_named`.
fn loaded(file: &Path, load: Load) -> zedc::run::Program {
    load(
        file.to_str().unwrap(),
        &[],
        &mut Default::default(),
        &mut Vec::new(),
    )
    .unwrap_or_else(|(status, why)| panic!("{}: status {status}: {why}", file.display()))
}

/// The signature of [`zedc::run::load_file`].
type Load = fn(
    &str,
    &[&str],
    &mut zedc::suppress::Suppress,
    &mut dyn std::io::Write,
) -> Result<zedc::run::Program, (u8, String)>;

/// The object file `zedc build` makes for the staged program `p`, with its debug sections
/// when `debug`.
fn object_of(p: &zedc::run::Program, debug: bool) -> Vec<u8> {
    let (g, sited) = lower_debug(&p.term(), Some(p.sites())).unwrap();
    zed_native::executable_object(
        g,
        true,
        p.ports(),
        &p.limits(),
        p.address().unwrap(),
        (p.file(), p.text()),
        &sited,
        debug,
    )
    .unwrap()
}

/// A relocation of a section, as `(offset, target, addend)`: the target is named by its
/// symbol, or by its section for a section's symbol, whose name is empty.
type Reloc = (u64, String, i64);

/// Each section of the object file `bytes` by name, with its bytes and its relocations. The
/// symbol table, the string tables and the relocation sections are left out: their bytes hold
/// symbol numbers, which the debug sections' own symbols shift, so each relocation is given
/// with its section, by its target's name, and the symbols by [`symbols`].
fn sections(bytes: &[u8]) -> BTreeMap<String, (Vec<u8>, Vec<Reloc>)> {
    let f = object::File::parse(bytes).unwrap();
    let section_name = |i| f.section_by_index(i).unwrap().name().unwrap().to_string();
    f.sections()
        .filter(|s| s.kind() != object::SectionKind::Metadata)
        .map(|s| {
            let relocations = s
                .relocations()
                .map(|(at, r)| {
                    let target = match r.target() {
                        RelocationTarget::Symbol(i) => {
                            let sym = f.symbol_by_index(i).unwrap();
                            match (sym.kind(), sym.section_index()) {
                                (SymbolKind::Section, Some(k)) => section_name(k),
                                _ => sym.name().unwrap().to_string(),
                            }
                        }
                        RelocationTarget::Section(k) => section_name(k),
                        t => format!("{t:?}"),
                    };
                    (at, target, r.addend())
                })
                .collect();
            let name = s.name().unwrap().to_string();
            (name, (s.data().unwrap().to_vec(), relocations))
        })
        .collect()
}

/// Each named symbol of the object file `bytes`, as `(name, section name, address, size)`.
fn symbols(bytes: &[u8]) -> Vec<(String, String, u64, u64)> {
    let f = object::File::parse(bytes).unwrap();
    let mut out: Vec<_> = f
        .symbols()
        .filter(|s| s.kind() != SymbolKind::Section && !s.name().unwrap().is_empty())
        .map(|s| {
            let section = (s.section_index())
                .map(|k| f.section_by_index(k).unwrap().name().unwrap().to_string())
                .unwrap_or_default();
            (
                s.name().unwrap().to_string(),
                section,
                s.address(),
                s.size(),
            )
        })
        .collect();
    out.sort();
    out
}

#[test]
fn the_code_is_the_same_with_and_without_debug_information() {
    let file = written("bytes", CHAIN);
    let (plain_bytes, debug_bytes) = (object_file(&file, false), object_file(&file, true));
    let (plain, debug) = (sections(&plain_bytes), sections(&debug_bytes));
    // The same symbols, at the same places; besides section symbols, a debug build adds only
    // the thread-local variables (`dwarf::define_debug_vars`, on x86-64) and the empty string
    // the keypath points at.
    let (plain_symbols, debug_symbols) = (symbols(&plain_bytes), symbols(&debug_bytes));
    for s in &plain_symbols {
        assert!(
            debug_symbols.contains(s),
            "{s:?} differs with debug information"
        );
    }
    let vars: Vec<_> = (debug_symbols.iter())
        .filter(|s| !plain_symbols.contains(s))
        .collect();
    let names: Vec<&str> = vars.iter().map(|s| s.0.as_str()).collect();
    let expected: &[&str] = match cfg!(target_arch = "x86_64") {
        true => &[
            "zed_debug_keypath",
            "zed_debug_keypath_root",
            "zed_debug_task",
        ],
        false => &[],
    };
    assert_eq!(names, expected);
    // Every section of the plain object, `.text` and `.eh_frame` among them, is in the debug
    // object with the same bytes and relocations.
    for name in [".text", ".eh_frame"] {
        assert!(plain.contains_key(name), "no {name} in {:?}", plain.keys());
    }
    for (name, s) in &plain {
        assert!(
            debug.get(name) == Some(s),
            "{name} differs with debug information"
        );
    }
    // The debug object adds only debug sections and a section of each of those symbols.
    let added: Vec<&String> = debug.keys().filter(|n| !plain.contains_key(*n)).collect();
    for name in &added {
        assert!(
            name.starts_with(".debug_") || vars.iter().any(|s| &s.1 == *name),
            "{name} added with debug information"
        );
    }
    for s in &vars {
        assert!(
            added.contains(&&s.1),
            "{s:?} in a section of the plain object"
        );
    }
    for name in [
        ".debug_info",
        ".debug_abbrev",
        ".debug_line",
        ".debug_rnglists",
    ] {
        assert!(added.contains(&&name.to_string()), "no {name} in {added:?}");
    }
    // The line table's addresses are relocations against the functions' symbols.
    let (_, line_relocations) = &debug[".debug_line"];
    assert!(
        line_relocations.iter().any(|(_, t, _)| t == "zed_root"),
        "{line_relocations:?}"
    );
}

#[test]
fn staging_for_names_keeps_the_graph_and_the_code() {
    // `zedc build` stages keeping the `let`s of the names the build made literals
    // (`Program::stage_named`), for the debugger; a literal lowers to no node, so the ZIR and
    // the code are those of `Program::stage`, which run and replay take. The programs: the
    // chain, one with folded lets of an integer, a float and a string (whose kept `let` must
    // still build; gdb shows its value, test
    // `gdb_prints_the_value_of_a_name_bound_to_a_constant_that_is_not_a_word`), and the step
    // programs.
    let folded = "main(m: MainArgs) {
    n = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1;
    c = 7;
    f = 1.5;
    s = \"hi\";
    k = n + c;
    m.stdout <- \"${k}\";
}
";
    let mut files = vec![
        written("names-chain", CHAIN),
        written("names-folded", folded),
    ];
    files.extend(
        (oracle::step_units().into_iter())
            .filter(|p| zedc::run::load(&std::fs::read(p).unwrap()).is_ok()),
    );
    assert_eq!(files.len(), 6);
    let root_names = |s: &zedc::zir::lower::Sited| -> Vec<String> {
        s.root.iter().map(|(x, _)| x.to_string()).collect()
    };
    for (i, file) in files.iter().enumerate() {
        let plain = loaded(file, zedc::run::load_file);
        let named = loaded(file, zedc::run::load_file_named);
        let (g, unnamed) = lower_debug(&plain.term(), Some(plain.sites())).unwrap();
        let (h, sited) = lower_debug(&named.term(), Some(named.sites())).unwrap();
        // The negative control: the folded names are kept by the one staging only, so the
        // two stagings do differ.
        if i == 1 {
            let (without, with) = (root_names(&unnamed), root_names(&sited));
            for x in ["c", "f", "s"] {
                assert!(!without.iter().any(|y| y == x), "{without:?}");
                assert!(with.iter().any(|y| y == x), "{with:?}");
            }
        }
        let shown = file.display();
        assert_eq!(
            zedc::zir::text::print(&g),
            zedc::zir::text::print(&h),
            "{shown}"
        );
        let (a, b) = (object_of(&plain, false), object_of(&named, false));
        assert!(sections(&a) == sections(&b), "{shown}: the objects differ");
        // With debug information too, the named program's code is the plain program's.
        let (a, b) = (sections(&a), sections(&object_of(&named, true)));
        for name in [".text", ".eh_frame"] {
            assert!(a.get(name) == b.get(name), "{shown}: {name} differs");
        }
    }
}

#[test]
fn two_debug_builds_of_a_program_are_the_same_bytes() {
    let file = written("twice", CHAIN);
    assert!(object_file(&file, true) == object_file(&file, true));
}

#[test]
fn the_call_frame_entries_are_relative_to_their_place() {
    // A position-independent executable cannot link an absolute address in the read-only
    // `.eh_frame` (ld.lld: "relocation R_X86_64_64 cannot be used against symbol 'zed_root'"),
    // so each function's start is written relative to its field, and `main` has an entry as
    // `zed_root` has.
    let file = written("frames", CHAIN);
    for debug in [false, true] {
        let bytes = object_file(&file, debug);
        let f = object::File::parse(&*bytes).unwrap();
        let eh = f.section_by_name(".eh_frame").unwrap();
        let mut targets = Vec::new();
        for (_, r) in eh.relocations() {
            assert_eq!(r.kind(), object::RelocationKind::Relative, "{r:?}");
            assert_eq!(r.size(), 32, "{r:?}");
            let RelocationTarget::Symbol(i) = r.target() else {
                panic!("{r:?}")
            };
            targets.push(f.symbol_by_index(i).unwrap().name().unwrap().to_string());
        }
        for name in ["zed_root", "main"] {
            assert!(
                targets.iter().any(|t| t == name),
                "{name} not in {targets:?}"
            );
        }
    }
}

/// gdb, or else gdb-multiarch, which the job's VM setup installs (wt/colab, `tools/farm_run.sh`
/// puts it on `PATH` as `gdb`).
fn gdb() -> &'static str {
    for g in ["gdb", "gdb-multiarch"] {
        let ran = Command::new(g)
            .arg("--version")
            .stdin(Stdio::null())
            .output();
        if ran.is_ok_and(|o| o.status.success()) {
            return g;
        }
    }
    panic!("neither gdb nor gdb-multiarch is on PATH");
}

/// What gdb writes, standard output then standard error, running `commands` in batch mode on
/// the executable `exe`.
fn under_gdb(exe: &Path, commands: &[&str]) -> String {
    let mut c = Command::new(gdb());
    c.args(["-batch", "-nx", "-q"]).env("DEBUGINFOD_URLS", "");
    for x in ["set pagination off", "set startup-with-shell off"]
        .iter()
        .chain(commands)
    {
        c.arg("-ex").arg(x);
    }
    let out = c.arg(exe).stdin(Stdio::null()).output().unwrap();
    String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
}

/// The program `src` of test `name` built, with the path of its source and of its executable.
fn executable_of(name: &str, src: &str) -> (PathBuf, PathBuf) {
    let file = written(name, src);
    let exe = file.with_extension("");
    built(&file, &exe);
    (file, exe)
}

/// The line of each stop gdb reports in `out` (`Breakpoint 2, zed_root () at d/f.zed:6`), in
/// order, for the file `file`.
fn stops(out: &str, file: &str) -> Vec<u32> {
    let at = format!("{file}:");
    out.lines()
        .filter(|l| l.starts_with("Breakpoint ") || l.starts_with("Temporary breakpoint "))
        .filter_map(|l| l.rsplit_once(&at)?.1.trim().parse().ok())
        .collect()
}

#[test]
fn gdb_stops_at_a_function_and_at_source_lines_and_walks_the_stack() {
    let (file, exe) = executable_of("stops", CHAIN);
    let name = "stops.zed";
    let out = under_gdb(
        &exe,
        &[
            "break zed_root",
            &format!("break {name}:2"),
            // Line 6, the send, has a row: a send takes its head's site (RT-sites-push).
            &format!("break {name}:6"),
            "run",
            "bt",
            "continue",
            "continue",
            "print 2 * 3",
            "show language",
            "continue",
        ],
    );
    // `zed_root`'s breakpoint may share line 2's address, and gdb then reports one stop there.
    let lines = stops(&out, name);
    assert!(
        (1..=6).contains(&lines[0])
            && lines.windows(2).all(|w| w[0] <= w[1])
            && lines.contains(&2)
            && lines.last() == Some(&6),
        "stops {lines:?} in {}:\n{out}",
        file.display()
    );
    // The backtrace walks from `zed_root` to its caller in the runtime by the call frame
    // information of `.eh_frame`, and ends at the runtime (zed/DEBUGGING.md: "Backtraces end
    // at the runtime"): `zed_root` runs on a stack `psm` switched to, which gdb cannot unwind
    // past to the C `main`.
    let bt: Vec<&str> = out.lines().filter(|l| l.starts_with('#')).collect();
    assert!(bt.first().is_some_and(|f| f.contains("zed_root")), "{out}");
    assert!(
        bt.get(1)
            .is_some_and(|f| f.contains("psm::") || f.contains("zed_rt::")),
        "{out}"
    );
    assert!(out.contains("$1 = 6"), "{out}");
    assert!(out.contains("exited normally"), "{out}");
}

#[test]
fn next_visits_a_functions_lines_in_source_order() {
    let (_, exe) = executable_of("next", CHAIN);
    let out = under_gdb(
        &exe,
        &["break next.zed:2", "run", "next", "next", "next", "next"],
    );
    // gdb writes each line it stops at as the line's number, a tab and its text.
    let visited: Vec<u32> = out
        .lines()
        .filter_map(|l| l.split_once('\t')?.0.parse().ok())
        .collect();
    assert!(
        visited.first() == Some(&2) && visited.windows(2).all(|w| w[0] < w[1]),
        "lines {visited:?}:\n{out}"
    );
    // Line 6, the send, has a row (RT-sites-push), so the fourth `next` stops there.
    assert_eq!(visited, [2, 3, 4, 5, 6], "{out}");
}

#[test]
fn the_lines_after_a_family_body_are_their_own() {
    // `map` is a `fam` node, whose body's nodes the generated code does not hold; the lines
    // after it are found by the numbers of their nodes, so `next` still visits 3, 4 and 5.
    let src = CHAIN.replacen("String(m.args)", "String(m.args.map((a) -> a ++ \"x\"))", 1);
    let (_, exe) = executable_of("family", &src);
    let out = under_gdb(&exe, &["break family.zed:2", "run", "next", "next", "next"]);
    let visited: Vec<u32> = out
        .lines()
        .filter_map(|l| l.split_once('\t')?.0.parse().ok())
        .collect();
    assert_eq!(visited, [2, 3, 4, 5], "{out}");
}

#[test]
fn gdb_prints_the_words_the_names_are_bound_to() {
    // Plan row DEBUG-dwarf-clif-bindings: at line 6, `n` and `k` are in the frame, each a
    // `zed_word` of its tag and payload, and the type names the tags. `c` and `f` are
    // constants: staging puts 7 in place of each read of `c` and reads `f` nowhere, and keeps
    // their `let`s for their names (`Program::stage_named`, which `zedc build` lowers), so
    // each is a constant word (`DW_OP_implicit_value`), the float's payload its bits.
    if !cfg!(target_arch = "x86_64") {
        return;
    }
    let src = "main(m: MainArgs) {
    n = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1;
    c = 7;
    f = 1.5;
    k = n + c;
    j = k * 3;
    m.stdout <- \"${j}\";
}
";
    let (_, exe) = executable_of("bindings", src);
    let out = under_gdb(
        &exe,
        &[
            "break bindings.zed:6",
            "run -- 5",
            "print n",
            "print k",
            "print c",
            "print f",
            "print k.bits - n.bits",
            "print k.tag",
            "info locals",
            "ptype k",
            "print m",
            "print m.args.bits - m.args.bits",
            "ptype m",
            "continue",
        ],
    );
    assert_eq!(stops(&out, "bindings.zed"), [6], "{out}");
    // On a failure, the names the lowering recorded from the staged program, as `zedc build`
    // lowers it, to tell a name never recorded from one the generator or the DWARF writer lost.
    let p = zedc::run::load(src.as_bytes()).unwrap().stage_named().0;
    let sited = lower_debug(&p.term(), Some(p.sites())).unwrap().1;
    let named = format!("names {:?}, root {:?}", sited.names, sited.root);
    // The bits of 1.5, 0x3FF8 << 48.
    let float = format!("$4 = {{tag = FLOAT, bits = {}}}", 1.5f64.to_bits() as i64);
    for want in [
        "$1 = {tag = INT, bits = 5}",
        "$2 = {tag = INT, bits = 12}",
        "$3 = {tag = INT, bits = 7}",
        float.as_str(),
        "$5 = 7",
        "$6 = INT",
        "type = struct zed_word",
        // `m` is the fields the program reads, here `m.args` (DEBUG-dwarf-clif-bindings).
        "$7 = {args = {tag = ",
        "$8 = 0",
        "type = struct MainArgs {",
        " args;",
        "exited normally",
    ] {
        assert!(out.contains(want), "no {want:?} in:\n{out}\n{named}");
    }
    let locals: Vec<&str> = (out.lines())
        .filter_map(|l| Some(l.split_once(" = {tag = ")?.0))
        .collect();
    for name in ["n", "c", "f", "k"] {
        assert!(
            locals.contains(&name),
            "no local {name} in:\n{out}\n{named}"
        );
    }
    // `j` is bound after line 6's code, and the run's output is 36.
    assert!(!locals.contains(&"j"), "{out}");
    assert!(out.contains("36"), "{out}");
}

#[test]
fn gdb_prints_the_value_of_a_name_bound_to_a_constant_that_is_not_a_word() {
    // Plan row FAIL-dwarf-staged-let-nonscalar: staging makes `s`, `t` and `u` literals and
    // keeps their `let`s for their names (`Program::stage_named`). `s` and `t` are read by no
    // code, so the table of constants has no entry for them; `u` is read, in place, by the
    // send. Each is shown as its value: a string's bytes (`zed_str`), the tuple's printed text
    // (`zed_text`), both as gdb prints a `char` array. `k` is still a word in the frame.
    if !cfg!(target_arch = "x86_64") {
        return;
    }
    let src = "main(m: MainArgs) {
    n = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1;
    s = \"hi\";
    t = (1, 2);
    u = \"yo\";
    k = n + 1;
    m.stdout <- \"${k}${u}\";
}
";
    let (_, exe) = executable_of("shown", src);
    let out = under_gdb(
        &exe,
        &[
            "break shown.zed:7",
            "run -- 5",
            "print s",
            "print t",
            "print u",
            "print k",
            "whatis s",
            "whatis t",
            "info locals",
            "continue",
        ],
    );
    assert_eq!(stops(&out, "shown.zed"), [7], "{out}");
    let p = zedc::run::load(src.as_bytes()).unwrap().stage_named().0;
    let sited = lower_debug(&p.term(), Some(p.sites())).unwrap().1;
    let named = format!("names {:?}, root {:?}", sited.names, sited.root);
    for want in [
        "$1 = \"hi\"",
        "$2 = \"(1, 2)\"",
        "$3 = \"yo\"",
        "$4 = {tag = INT, bits = 6}",
        "type = zed_str",
        "type = zed_text",
        "exited normally",
    ] {
        assert!(out.contains(want), "no {want:?} in:\n{out}\n{named}");
    }
    // `info locals` lists the names of the inner blocks too.
    for want in ["s = \"hi\"", "t = \"(1, 2)\"", "u = \"yo\""] {
        assert!(out.contains(want), "no local {want:?} in:\n{out}\n{named}");
    }
    assert!(out.contains("6yo"), "{out}");
}

#[test]
fn gdb_prints_a_name_a_lambda_captures_inside_its_body() {
    // zed/DEBUGGING.md: every binding in scope, and a name bound outside a lambda is in scope
    // in its body. The body reads `c` from the closure into its own frame at its start, so at
    // line 5, in the body's function and not `zed_root`, `c` is a local and `v` an argument.
    // The lambda is called through a tuple, so it is a function of its own.
    if !cfg!(target_arch = "x86_64") {
        return;
    }
    let src = "main(m: MainArgs) {
    n = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1;
    c = n * 2;
    f = (v) ->
        v + c;
    t = (f, n);
    m.stdout <- \"${t[0](t[1])}\";
}
";
    let (_, exe) = executable_of("captures", src);
    let out = under_gdb(
        &exe,
        &[
            "break captures.zed:5",
            "run -- 5",
            "bt 1",
            "print c",
            "print v",
            "info args",
            "info locals",
            "continue",
        ],
    );
    assert_eq!(stops(&out, "captures.zed"), [5], "{out}");
    let top = (out.lines().find(|l| l.starts_with("#0 "))).unwrap_or_else(|| panic!("{out}"));
    assert!(
        !top.contains("zed_root"),
        "the stop is not in the body: {top}\n{out}"
    );
    for want in [
        "$1 = {tag = INT, bits = 10}",
        "$2 = {tag = INT, bits = 5}",
        "v = {tag = INT, bits = 5}",
        "c = {tag = INT, bits = 10}",
        "exited normally",
    ] {
        assert!(out.contains(want), "no {want:?} in:\n{out}");
    }
    // `v` is the parameter and `c` a capture: `info args` comes before `info locals`.
    let (args, locals) = (out.find("v = {"), out.find("c = {tag"));
    assert!(args < locals, "{out}");
    assert!(out.contains("15"), "{out}");
}

#[test]
fn a_conditioned_breakpoint_stops_only_when_its_condition_holds() {
    // zed/DEBUGGING.md section 6: `break file.zed:12 if zed_debug_task == 17`. The serial
    // runtime runs only task 0, so the breakpoint on task 17 never stops, nor the one whose
    // condition is false whatever the task; the one on task 0 does.
    let (_, exe) = executable_of("condition", CHAIN);
    let out = under_gdb(
        &exe,
        &[
            "break condition.zed:3 if zed_debug_task == 17",
            "break condition.zed:4 if 1 == 0",
            "break condition.zed:5 if zed_debug_task == 0",
            "run",
            "continue",
        ],
    );
    assert_eq!(stops(&out, "condition.zed"), [5], "{out}");
    assert!(!out.contains("Error in testing"), "{out}");
    assert!(out.contains("exited normally"), "{out}");
}

#[test]
fn the_thread_local_variables_are_offsets_in_the_thread_local_block() {
    // Each variable's location in `.debug_info` is `DW_OP_const8u` (0x0e), an
    // `R_X86_64_DTPOFF64` relocation to the variable, then `DW_OP_form_tls_address` (0x9b);
    // each variable is in a section kept by the link's `--gc-sections` (`SHF_GNU_RETAIN`).
    if !cfg!(target_arch = "x86_64") {
        return;
    }
    let bytes = object_file(&written("tls", CHAIN), true);
    let f = object::File::parse(&*bytes).unwrap();
    let info = f.section_by_name(".debug_info").unwrap();
    let data = info.data().unwrap();
    let mut found = Vec::new();
    for (at, r) in info.relocations() {
        let RelocationTarget::Symbol(i) = r.target() else {
            continue;
        };
        let sym = f.symbol_by_index(i).unwrap();
        let name = sym.name().unwrap();
        if !name.starts_with("zed_debug_") {
            continue;
        }
        let at = usize::try_from(at).unwrap();
        assert_eq!(
            r.flags(),
            object::RelocationFlags::Elf {
                r_type: object::elf::R_X86_64_DTPOFF64
            },
            "{name}"
        );
        assert_eq!((data[at - 1], data[at + 8]), (0x0e, 0x9b), "{name}");
        let section = f.section_by_index(sym.section_index().unwrap()).unwrap();
        let object::SectionFlags::Elf { sh_flags, .. } = section.flags() else {
            panic!("{name}: {:?}", section.flags())
        };
        let want = object::elf::SHF_TLS.0 | object::elf::SHF_GNU_RETAIN.0;
        assert_eq!(sh_flags.0 & want, want, "{name}");
        found.push(name.to_string());
    }
    found.sort();
    assert_eq!(found, ["zed_debug_keypath", "zed_debug_task"]);
}

/// Whether gdb's output `out` reports a stop at a line of the file `name`.
fn stops_at_a_line(out: &str, name: &str) -> bool {
    !stops(out, name).is_empty()
}

/// gdb on the executable `exe` of the program file `name`: stopped at `zed_root` under a
/// condition on the task that holds, it reports the stop at a line of `name` (`Err("line")`
/// when it does not), prints task 0 and the root's empty keypath; under a condition on task
/// 17, which no stop meets, the program runs to its end.
fn under_gdb_with_the_task(exe: &Path, name: &str) -> Result<(), (&'static str, String)> {
    let out = under_gdb(
        exe,
        &[
            "break zed_root if zed_debug_task == 0",
            "run",
            "print zed_debug_task",
            "print zed_debug_keypath",
            "continue",
        ],
    );
    if !stops_at_a_line(&out, name) {
        return Err(("line", out));
    }
    let printed: Vec<&str> = out.lines().filter(|l| l.starts_with('$')).collect();
    if printed.len() != 2 || !printed[0].ends_with(" = 0") || !printed[1].ends_with(" \"\"") {
        return Err(("print", out));
    }
    let out = under_gdb(exe, &["break zed_root if zed_debug_task == 17", "run"]);
    let ended = out.contains("exited normally") || out.contains("exited with code");
    if out.contains("Breakpoint 1,") || out.contains("Error in testing") || !ended {
        return Err(("condition", out));
    }
    Ok(())
}

#[test]
fn gdb_reads_the_task_on_each_step_program_and_enabled_corpus_program() {
    // The programs among the step units (`agreement::the_step_programs_are_exactly_these`),
    // and the enabled corpus programs: none yet, as the corpus begins at L3.
    let mut programs: Vec<_> = oracle::step_units()
        .into_iter()
        .filter(|p| zedc::run::load(&std::fs::read(p).unwrap()).is_ok())
        .collect();
    assert_eq!(programs.len(), 4);
    let enabled: Vec<_> = (oracle::corpus().into_iter())
        .filter(|(_, l)| *l <= ENABLED)
        .map(|(p, _)| p)
        .collect();
    assert_eq!(enabled.len(), 0);
    programs.extend(enabled);
    // Each program on a thread of its own: each is mostly the link's wait and gdb's start. The
    // scratch directories are claimed on the test's thread, which bears the test's name.
    let exes: Vec<PathBuf> = (programs.iter())
        .map(|src| {
            let stem = src.file_stem().unwrap().to_string_lossy();
            dir(&format!("dwarf/task-{stem}")).join(&*stem)
        })
        .collect();
    std::thread::scope(|s| {
        for (src, exe) in programs.iter().zip(&exes) {
            s.spawn(move || {
                built(src, exe);
                let name = src.file_name().unwrap().to_string_lossy();
                if let Err((check, out)) = under_gdb_with_the_task(exe, &name) {
                    panic!("{}: the {check} check fails:\n{out}", src.display());
                }
            });
        }
    });
}

#[test]
fn an_executable_with_no_line_table_fails_the_line_check() {
    // The negative control of the test above: with `.debug_line` removed, gdb finds no line
    // for the stop at `zed_root`.
    let (file, exe) = executable_of("no_lines", CHAIN);
    let stripped = exe.with_file_name("no_lines-stripped");
    let ran = Command::new("objcopy")
        .args(["--remove-section", ".debug_line"])
        .arg(&exe)
        .arg(&stripped)
        .output()
        .unwrap();
    assert!(ran.status.success(), "{ran:?}");
    let name = file.file_name().unwrap().to_string_lossy();
    assert_eq!(under_gdb_with_the_task(&exe, &name), Ok(()));
    let failed = under_gdb_with_the_task(&stripped, &name);
    assert!(matches!(&failed, Err(("line", _))), "{failed:?}");
    // The failed check is printed, so a run with `--nocapture` shows the control fired.
    eprintln!("negative control: the stripped executable gives {failed:?}");
}

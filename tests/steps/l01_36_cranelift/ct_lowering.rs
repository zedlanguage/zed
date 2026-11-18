//! What Cranelift 0.137.1 emits for the forms `@cryptosafe` lowers to (DESIGN sec:security,
//! step L33.1f; cross-review XR-ct-enforce, round 1). The design rests on these facts about
//! the code generator, so each is pinned here: a newer Cranelift that changes one fails a test
//! and the design's text is checked again.
//!
//! - `select_spectre_guard` on a value in general registers is a `cmov` with no conditional
//!   branch, and on a float or a vector it branches; so `ctselect` lowers by type, and a float
//!   or a vector takes `bitselect` with a full-width mask, or goes through its bits.
//! - Division by a constant becomes multiplication only for 32- and 64-bit integers and only
//!   when the optimizer runs (opt_level is not none); so zedc rewrites such a division itself.
//! - A store just before a return is kept (alias analysis treats a return as reading all
//!   memory), and a store overwritten before any read is removed; so a wipe written as plain
//!   stores survives Cranelift, and the negative control of step L33.1g must make the wipe dead
//!   some other way.
//! - (Round 2.) Under the host's features, which zed-native takes, the bit counts use
//!   `popcnt`, `lzcnt` and `tzcnt`; with the features off, `clz` and `ctz` still use `bsr` and
//!   `bsf`; all five are off Intel's list, so zedc lowers the bit counts of a secret itself.
//! - (Round 2, corrected in round 3.) A float spill is a 16-byte `movdqu`, on Intel's list; an
//!   `f64`-typed store is SSE `movsd`, not on it.
//!
//! The checks read Cranelift's own listing of the machine instructions it chose
//! (`Context::set_disasm`), on x86-64 only (the first release's target). Each pseudo-instruction
//! that expands to a branch is listed with that branch (the float select prints
//! `movsd ...; jnz $next; ...`); the round-1 seats disassembled the emitted bytes with objdump
//! and found the same branches and `cmov`s. The cases that branch are the negative controls
//! of the cases that must not: the same check that finds no branch in one finds the branch in
//! the other.

use cranelift_codegen::Context;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use std::str::FromStr;

/// The selects. Every argument stands for a secret.
const SELECTS: &str = "
function %sg_i64(i64, i64, i64, i64) -> i64 {
block0(v0: i64, v1: i64, v2: i64, v3: i64):
    v4 = icmp eq v0, v1
    v5 = select_spectre_guard v4, v2, v3
    return v5
}
function %sg_i128(i64, i64, i128, i128) -> i128 {
block0(v0: i64, v1: i64, v2: i128, v3: i128):
    v4 = icmp eq v0, v1
    v5 = select_spectre_guard v4, v2, v3
    return v5
}
function %sg_f64(i64, i64, f64, f64) -> f64 {
block0(v0: i64, v1: i64, v2: f64, v3: f64):
    v4 = icmp eq v0, v1
    v5 = select_spectre_guard v4, v2, v3
    return v5
}
function %sg_i8x16(i64, i64, i8x16, i8x16) -> i8x16 {
block0(v0: i64, v1: i64, v2: i8x16, v3: i8x16):
    v4 = icmp eq v0, v1
    v5 = select_spectre_guard v4, v2, v3
    return v5
}
function %mask_i8x16(i64, i64, i8x16, i8x16) -> i8x16 {
block0(v0: i64, v1: i64, v2: i8x16, v3: i8x16):
    v4 = icmp eq v0, v1
    v5 = bmask.i8 v4
    v6 = splat.i8x16 v5
    v7 = bitselect v6, v2, v3
    return v7
}
function %bits_f64(i64, i64, f64, f64) -> f64 {
block0(v0: i64, v1: i64, v2: f64, v3: f64):
    v4 = icmp eq v0, v1
    v5 = bitcast.i64 v2
    v6 = bitcast.i64 v3
    v7 = select_spectre_guard v4, v5, v6
    v8 = bitcast.f64 v7
    return v8
}
";

/// Division and remainder by 3329, the modulus of ML-KEM (KyberSlash divided by it).
const DIVISIONS: &str = "
function %udiv_u16(i16) -> i16 {
block0(v0: i16):
    v1 = iconst.i16 3329
    v2 = udiv v0, v1
    return v2
}
function %udiv_u32(i32) -> i32 {
block0(v0: i32):
    v1 = iconst.i32 3329
    v2 = udiv v0, v1
    return v2
}
function %urem_u64(i64) -> i64 {
block0(v0: i64):
    v1 = iconst.i64 3329
    v2 = urem v0, v1
    return v2
}
";

/// A wipe before a return, and a store overwritten before any read.
const STORES: &str = "
function %wipe_before_return(i64) {
block0(v0: i64):
    v1 = iconst.i64 0
    store v1, v0
    return
}
function %overwritten(i64) {
block0(v0: i64):
    v1 = iconst.i64 0
    store v1, v0
    v2 = iconst.i64 119
    store v2, v0
    return
}
";

/// The bit counts of a secret, which zedc lowers itself (round 2).
const BIT_COUNTS: &str = "
function %popcnt_u64(i64) -> i64 {
block0(v0: i64):
    v1 = popcnt v0
    return v1
}
function %clz_u64(i64) -> i64 {
block0(v0: i64):
    v1 = clz v0
    return v1
}
function %ctz_u64(i64) -> i64 {
block0(v0: i64):
    v1 = ctz v0
    return v1
}
";

/// An `f64` live across a call: System V saves no `xmm` register, so it is spilled.
const F64_ACROSS_CALL: &str = "
function %f64_across_call(f64) -> f64 {
    sig0 = () system_v
    fn0 = %g sig0
block0(v0: f64):
    call fn0()
    return v0
}
";

/// Cranelift's listing of each function in `clif`, by name, at `opt_level`.
fn listings(clif: &str, opt_level: &str) -> Vec<(String, String)> {
    listings_with(clif, &[("opt_level", opt_level)], &[])
}

/// Cranelift's listing of each function in `clif`, by name, with the shared settings `flags`
/// and the x86-64 settings `isa_flags` (the host's features, as zed-native takes them).
fn listings_with(
    clif: &str,
    flags: &[(&str, &str)],
    isa_flags: &[(&str, &str)],
) -> Vec<(String, String)> {
    let mut b = settings::builder();
    b.set("enable_llvm_abi_extensions", "true").unwrap();
    for (k, v) in flags {
        b.set(k, v).unwrap();
    }
    let triple = target_lexicon::Triple::from_str("x86_64-unknown-linux-gnu").unwrap();
    let mut ib = isa::lookup(triple).unwrap();
    for (k, v) in isa_flags {
        ib.set(k, v).unwrap();
    }
    let isa = ib.finish(settings::Flags::new(b)).unwrap();
    cranelift_reader::parse_functions(clif)
        .unwrap()
        .into_iter()
        .map(|f| {
            let name = f.name.to_string().trim_start_matches('%').to_string();
            let mut ctx = Context::for_function(f);
            ctx.set_disasm(true);
            let code = ctx.compile(&*isa, &mut ControlPlane::default()).unwrap();
            (name, code.vcode.clone().unwrap())
        })
        .collect()
}

/// The listing of `name`.
fn listing<'a>(all: &'a [(String, String)], name: &str) -> &'a str {
    &all.iter().find(|(n, _)| n == name).unwrap().1
}

/// The x86-64 conditional jumps in a listing (`jnz`, `jb`, ...; `jmp` and the listing's
/// unconditional `j` are not).
fn conditional_jumps(text: &str) -> Vec<&str> {
    const CONDITIONS: [&str; 30] = [
        "o", "no", "b", "nb", "c", "nc", "ae", "nae", "z", "nz", "e", "ne", "be", "nbe", "a", "na",
        "s", "ns", "p", "np", "pe", "po", "l", "nl", "ge", "nge", "le", "nle", "g", "ng",
    ];
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|w| w.strip_prefix('j').is_some_and(|c| CONDITIONS.contains(&c)))
        .collect()
}

/// The division instructions in a listing.
fn divisions(text: &str) -> usize {
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|w| matches!(*w, "divw" | "divl" | "divq" | "idivw" | "idivl" | "idivq"))
        .count()
}

/// The stores to the address in `%rdi`, the first argument.
fn stores_through_first_argument(text: &str) -> usize {
    text.lines()
        .filter(|l| l.trim_start().starts_with("mov") && l.trim_end().ends_with("(%rdi)"))
        .count()
}

#[test]
fn a_select_in_general_registers_has_no_branch_and_one_of_a_float_or_vector_has_one() {
    for opt in ["none", "speed"] {
        let all = listings(SELECTS, opt);
        for name in ["sg_i64", "sg_i128", "mask_i8x16", "bits_f64"] {
            let text = listing(&all, name);
            assert_eq!(
                conditional_jumps(text),
                Vec::<&str>::new(),
                "{name} at {opt}:\n{text}"
            );
        }
        assert!(listing(&all, "sg_i64").contains("cmov"), "sg_i64 at {opt}");
        // The negative controls, and the reason `ctselect` lowers by type.
        for name in ["sg_f64", "sg_i8x16"] {
            let text = listing(&all, name);
            assert_eq!(conditional_jumps(text).len(), 1, "{name} at {opt}:\n{text}");
        }
    }
}

#[test]
fn a_division_by_a_constant_is_a_multiplication_only_at_32_and_64_bits_with_the_optimizer() {
    let none = listings(DIVISIONS, "none");
    let speed = listings(DIVISIONS, "speed");
    for name in ["udiv_u16", "udiv_u32", "urem_u64"] {
        let text = listing(&none, name);
        assert_eq!(divisions(text), 1, "{name} at none:\n{text}");
    }
    assert_eq!(
        divisions(listing(&speed, "udiv_u16")),
        1,
        "udiv_u16 at speed"
    );
    for name in ["udiv_u32", "urem_u64"] {
        let text = listing(&speed, name);
        assert_eq!(divisions(text), 0, "{name} at speed:\n{text}");
    }
}

#[test]
fn a_store_before_a_return_is_kept_and_an_overwritten_store_is_removed() {
    let all = listings(STORES, "speed");
    let text = listing(&all, "wipe_before_return");
    assert_eq!(stores_through_first_argument(text), 1, "{text}");
    // The negative control: the first of two stores to one address is removed, so the check
    // above sees a removal when there is one.
    let text = listing(&all, "overwritten");
    assert_eq!(stores_through_first_argument(text), 1, "{text}");
}

/// The words of a listing that name one of `mnemonics`, with or without a size suffix.
fn uses(text: &str, mnemonics: &[&str]) -> Vec<String> {
    text.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|w| {
            mnemonics.iter().any(|m| {
                w.strip_prefix(m)
                    .is_some_and(|s| matches!(s, "" | "w" | "l" | "q"))
            })
        })
        .map(str::to_string)
        .collect()
}

#[test]
fn bit_counts_use_instructions_off_intels_list_only_under_the_hosts_features() {
    // Round 2 (CT-STUDY.md): POPCNT, LZCNT, TZCNT, BSR and BSF are not on Intel's DOIT list,
    // and zed-native takes the host's features, so zedc lowers the bit counts of a secret
    // itself and compiles secret code with these features off.
    const OFF_LIST: [&str; 5] = ["popcnt", "lzcnt", "tzcnt", "bsr", "bsf"];
    // A host with these features also has SSE4.2, which Cranelift's `use_popcnt` requires
    // (cranelift-codegen 0.137.1 src/isa/x64/lower/isle.rs:516-517).
    let host = [
        ("has_sse3", "true"),
        ("has_ssse3", "true"),
        ("has_sse41", "true"),
        ("has_sse42", "true"),
        ("has_popcnt", "true"),
        ("has_lzcnt", "true"),
        ("has_bmi1", "true"),
    ];
    let on = listings_with(BIT_COUNTS, &[("opt_level", "speed")], &host);
    for (name, mnemonic) in [
        ("popcnt_u64", "popcnt"),
        ("clz_u64", "lzcnt"),
        ("ctz_u64", "tzcnt"),
    ] {
        let text = listing(&on, name);
        assert!(
            !uses(text, &[mnemonic]).is_empty(),
            "{name} with the host's features:\n{text}"
        );
    }
    // Features off: the popcount is a sequence of shifts, masks and additions, but the leading
    // and trailing counts still use `bsr` and `bsf`, also off the list; so zedc must lower all
    // three itself and turning the features off is not enough on its own.
    let off = listings_with(BIT_COUNTS, &[("opt_level", "speed")], &[]);
    let text = listing(&off, "popcnt_u64");
    assert_eq!(
        uses(text, &OFF_LIST),
        Vec::<String>::new(),
        "popcnt_u64 off:\n{text}"
    );
    for name in ["clz_u64", "ctz_u64"] {
        let text = listing(&off, name);
        assert!(
            !uses(text, &["bsr", "bsf"]).is_empty(),
            "{name} off:\n{text}"
        );
    }
}

/// An `f64` stored to memory by the program, not by the register allocator.
const F64_STORE: &str = "
function %f64_store(f64, i64) {
block0(v0: f64, v1: i64):
    store v0, v1
    return
}
";

/// The mnemonics of the moves to or from the stack in a listing.
fn stack_moves(text: &str) -> Vec<String> {
    text.lines()
        .filter(|l| l.contains("(%rsp)") && l.trim_start().starts_with("mov"))
        .map(|l| l.split_whitespace().next().unwrap().to_string())
        .collect()
}

#[test]
fn a_float_spills_with_movdqu_and_a_stored_f64_uses_sse_movsd() {
    // The register allocator spills every float-class register as a 16-byte vector
    // (machinst/abi.rs `gen_spill` with `canonical_type_for_rc`, x64 inst/mod.rs 1432-1438), so
    // an `f64` live across a call is saved with `movdqu`, which is on Intel's list; round 2 said
    // `movsd`, wrongly. An `f64`-typed store is SSE `movsd` (inst/mod.rs 347-357), which is not
    // on the list (its MOVSD rows are the string move, opcode A5): one reason a secret `f64` is
    // held as the integer of its bits. The `i64` spill (`movq`) is the control that the
    // spill-finding check finds a spill of the other register class.
    let as_i64 = F64_ACROSS_CALL.replace("f64", "i64");
    for alloc in ["backtracking", "single_pass"] {
        for opt in ["none", "speed"] {
            let flags = [("opt_level", opt), ("regalloc_algorithm", alloc)];
            let all = listings_with(F64_ACROSS_CALL, &flags, &[]);
            let text = listing(&all, "f64_across_call");
            let moves = stack_moves(text);
            assert!(
                moves.iter().any(|m| m == "movdqu"),
                "{alloc} {opt}:\n{text}"
            );
            assert!(
                !moves.iter().any(|m| m == "movsd"),
                "{alloc} {opt}:\n{text}"
            );
            let all = listings_with(&as_i64, &flags, &[]);
            let text = listing(&all, "i64_across_call");
            let moves = stack_moves(text);
            assert!(
                moves.iter().any(|m| m == "movq"),
                "{alloc} {opt}, i64:\n{text}"
            );
            assert!(
                !moves.iter().any(|m| m == "movdqu"),
                "{alloc} {opt}, i64:\n{text}"
            );
            let all = listings_with(F64_STORE, &flags, &[]);
            let text = listing(&all, "f64_store");
            assert!(
                !uses(text, &["movsd"]).is_empty(),
                "{alloc} {opt}, store:\n{text}"
            );
        }
    }
}

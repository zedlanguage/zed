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

/// Cranelift's listing of each function in `clif`, by name, at `opt_level`.
fn listings(clif: &str, opt_level: &str) -> Vec<(String, String)> {
    let mut b = settings::builder();
    b.set("opt_level", opt_level).unwrap();
    b.set("enable_llvm_abi_extensions", "true").unwrap();
    let triple = target_lexicon::Triple::from_str("x86_64-unknown-linux-gnu").unwrap();
    let isa = isa::lookup(triple)
        .unwrap()
        .finish(settings::Flags::new(b))
        .unwrap();
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

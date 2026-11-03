//! The reference programs of the corpus. Each computes the expected output of the corpus program
//! of its number, directly in Rust. This crate does not depend on the compiler: the corpus tests
//! the compiler, so the outputs must not come from it.

/// Appends a formatted line to the output.
macro_rules! say {
    ($out:expr, $($arg:tt)*) => {
        std::fmt::Write::write_fmt($out, format_args!("{}\n", format_args!($($arg)*)))
            .expect("writing to a String")
    };
}

pub mod zedrt;

mod p01;
mod p02;
mod p03;
mod p04;
mod p05;
mod p06;
mod p07;
mod p08;
mod p09;
mod p10;
mod p11;
mod p12;
mod p13;
mod p14;
mod p15;
mod p16;
mod p17;
mod p18;
mod p19;
mod p20;
mod p21;
mod p22;
mod p23;
mod p24;
mod p25;
mod p26;
mod p27;
mod p28;
mod p29;
mod p30;
mod p31;

/// A program: the input's lines and the output so far, which an error leaves in place.
pub type Program = fn(&[String], &mut String) -> Result<(), String>;

/// The programs, by number from 1.
const PROGRAMS: [Program; 31] = [
    p01::run,
    p02::run,
    p03::run,
    p04::run,
    p05::run,
    p06::run,
    p07::run,
    p08::run,
    p09::run,
    p10::run,
    p11::run,
    p12::run,
    p13::run,
    p14::run,
    p15::run,
    p16::run,
    p17::run,
    p18::run,
    p19::run,
    p20::run,
    p21::run,
    p22::run,
    p23::run,
    p24::run,
    p25::run,
    p26::run,
    p27::run,
    p28::run,
    p29::run,
    p30::run,
    p31::run,
];

/// The program numbered `number`, as the first two characters of a corpus file's name.
pub fn program(number: &str) -> Option<Program> {
    let i: usize = number.parse().ok()?;
    PROGRAMS.get(i.checked_sub(1)?).copied()
}

/// The output of program `number` on the input file at `input`, up to any error, and the error.
pub fn run(number: &str, input: &str) -> (String, Result<(), String>) {
    let mut out = String::new();
    let result = match (program(number), zedrt::read_lines(input)) {
        (None, _) => Err(format!("no reference program {number}")),
        (Some(_), Err(e)) => Err(e),
        (Some(f), Ok(lines)) => f(&lines, &mut out),
    };
    (out, result)
}

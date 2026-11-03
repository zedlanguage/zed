//! 10 HH:MM matcher. The output is the language of ([01][0-9]|2[0-3]):[0-5][0-9], tested
//! directly, anchored at both ends; the program also runs the corpus program's own algorithm
//! (Brzozowski derivatives, transcribed from 10-regex-matcher/regex.zed) and stops if the two
//! disagree on any line.

use std::rc::Rc;

enum Re {
    Void,
    Eps,
    Lit(char),
    Range(char, char),
    Seq(Rc<Re>, Rc<Re>),
    Alt(Rc<Re>, Rc<Re>),
}

use Re::{Alt, Eps, Lit, Range, Seq, Void};

fn nullable(r: &Re) -> bool {
    match r {
        Void | Lit(_) | Range(..) => false,
        Eps => true,
        Seq(a, b) => nullable(a) && nullable(b),
        Alt(a, b) => nullable(a) || nullable(b),
    }
}

fn deriv(r: &Rc<Re>, ch: char) -> Rc<Re> {
    let eps_if = |hit: bool| Rc::new(if hit { Eps } else { Void });
    match &**r {
        Void | Eps => Rc::new(Void),
        Lit(c) => eps_if(*c == ch),
        Range(lo, hi) => eps_if(*lo <= ch && ch <= *hi),
        Seq(a, b) if nullable(a) => {
            Rc::new(Alt(Rc::new(Seq(deriv(a, ch), Rc::clone(b))), deriv(b, ch)))
        }
        Seq(a, b) => Rc::new(Seq(deriv(a, ch), Rc::clone(b))),
        Alt(a, b) => Rc::new(Alt(deriv(a, ch), deriv(b, ch))),
    }
}

fn matches_re(r: &Rc<Re>, s: &str) -> bool {
    let end = s.chars().fold(Rc::clone(r), |r, c| deriv(&r, c));
    nullable(&end)
}

fn seq(a: Rc<Re>, b: Rc<Re>) -> Rc<Re> {
    Rc::new(Seq(a, b))
}

fn rng(a: char, b: char) -> Rc<Re> {
    Rc::new(Range(a, b))
}

fn is_hhmm(line: &str) -> bool {
    match line.as_bytes() {
        [h, m, b':', t, u] => {
            let hour = matches!(h, b'0' | b'1') && m.is_ascii_digit()
                || *h == b'2' && matches!(m, b'0'..=b'3');
            hour && matches!(t, b'0'..=b'5') && u.is_ascii_digit()
        }
        _ => false,
    }
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let hours = Rc::new(Alt(
        seq(rng('0', '1'), rng('0', '9')),
        seq(Rc::new(Lit('2')), rng('0', '3')),
    ));
    let minutes = seq(Rc::new(Lit(':')), seq(rng('0', '5'), rng('0', '9')));
    let hhmm = seq(hours, minutes);
    for line in lines {
        let ok = is_hhmm(line);
        if ok != matches_re(&hhmm, line) {
            return Err(format!("the test and the derivatives disagree: {line}"));
        }
        say!(out, "{}{line}", if ok { "yes " } else { "no " });
    }
    Ok(())
}

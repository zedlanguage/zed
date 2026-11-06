//! The address of a diagnostic and its suppression (DESIGN.md sec:diagnostics, item
//! DIAG-suppress). Each diagnostic has an address, printed under it as `address: <hex>`, that
//! is the same on every run of the same source; `--suppress <address>` on `zedc run`,
//! `replay`, `build` and `test` leaves the warning at that address unprinted. The program is
//! the same with or without it: suppression changes only what is printed. A rejection cannot
//! be suppressed, and an address that names nothing is reported.

mod addresses;

use std::collections::HashMap;

use crate::address::ContentAddress;
use crate::front::Diagnostic;

pub use addresses::Severity;
pub(crate) use addresses::addresses;

/// The addresses `--suppress` names on a command line, each with whether a diagnostic had it.
#[derive(Default, Debug)]
pub struct Suppress {
    named: Vec<ContentAddress>,
    matched: HashMap<ContentAddress, bool>,
}

impl Suppress {
    /// The words of `words` other than each `--suppress <address>`, and the addresses those
    /// name; or why a word after `--suppress` is not an address, or is missing.
    pub fn take<'a>(words: &[&'a str]) -> Result<(Suppress, Vec<&'a str>), String> {
        let mut suppress = Suppress::default();
        let mut rest = Vec::with_capacity(words.len());
        let mut words = words.iter();
        while let Some(&w) = words.next() {
            if w != "--suppress" {
                rest.push(w);
                continue;
            }
            let hex = words
                .next()
                .ok_or("`--suppress` needs an address, 64 lowercase hex digits")?;
            let a = ContentAddress::parse(hex).ok_or_else(|| {
                format!("`--suppress {hex}`: an address is 64 lowercase hex digits")
            })?;
            if suppress.matched.insert(a, false).is_none() {
                suppress.named.push(a);
            }
        }
        Ok((suppress, rest))
    }

    /// Whether the warning `w` is suppressed; its address is then counted as matched.
    pub fn hides(&mut self, w: &Diagnostic) -> bool {
        self.matched.get_mut(&w.address).is_some_and(|m| {
            *m = true;
            true
        })
    }

    /// A line for each rejection of `rejections`, of the unit read from `file`, whose
    /// address is named: a rejection cannot be suppressed. The address counts as matched.
    pub fn refused(&mut self, file: &str, rejections: &[Diagnostic]) -> Vec<String> {
        let mut out = Vec::new();
        for d in rejections {
            if let Some(m) = self.matched.get_mut(&d.address) {
                *m = true;
                out.push(format!(
                    "{file}:{}:{}: `--suppress {}` names a rejection, which cannot be suppressed",
                    d.line, d.col, d.address
                ));
            }
        }
        out
    }

    /// A line for each address named that no diagnostic had, in the order named.
    pub fn unmatched(&self) -> Vec<String> {
        self.named
            .iter()
            .filter(|a| !self.matched[*a])
            .map(|a| format!("`--suppress {a}`: no diagnostic has this address"))
            .collect()
    }
}

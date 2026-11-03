//! 15 spreadsheet: after each edit, every cell's value in name order (code-point order). A term
//! is an integer when int() reads it (try_parse_int), else a cell name; an empty cell is 0. #set
//! inserts or replaces. A cell that depends on itself has no value: it is an error.
//!
//! A formula is kept as a constant and each name's multiplicity. An edit changes only the cell
//! it names and the cells that depend on that one, so it walks them in dependency order and
//! hands each its change in value: one visit per dependency edge. Cells depend on cells as
//! deeply as the input says, so the walks keep their own stacks.

use std::collections::hash_map::Keys;
use std::collections::{BTreeMap, HashMap};
use std::mem;
use std::str::Split;

use num_bigint::BigInt;
use num_traits::Zero;

use crate::zedrt::try_parse_int;

/// Every name that a line defined or a formula read, by index.
#[derive(Default)]
struct Sheet<'a> {
    index: HashMap<&'a str, usize>,
    names: Vec<&'a str>,
    /// The cells each cell's formula names, with how many times.
    uses: Vec<Vec<(usize, u64)>>,
    /// The cells whose formulas name each cell, with how many times.
    users: Vec<HashMap<usize, u64>>,
    values: Vec<BigInt>,
    /// `name=value` of each defined cell, as it is printed.
    shown: Vec<String>,
    /// The change in value each cell has yet to hand on, during an edit.
    changes: Vec<BigInt>,
    /// The last edit whose walk reached each cell.
    seen: Vec<usize>,
}

impl<'a> Sheet<'a> {
    /// The cell `name`, made if it is new.
    fn cell(&mut self, name: &'a str) -> usize {
        if let Some(&c) = self.index.get(name) {
            return c;
        }
        let c = self.names.len();
        self.index.insert(name, c);
        self.names.push(name);
        self.uses.push(Vec::new());
        self.users.push(HashMap::new());
        self.values.push(BigInt::zero());
        self.shown.push(String::new());
        self.changes.push(BigInt::zero());
        self.seen.push(0);
        c
    }

    /// Gives `edited` the formula `formula` as its constant and names.
    fn set_formula(&mut self, edited: usize, formula: &'a str) -> BigInt {
        let mut value = BigInt::zero();
        let mut counts: HashMap<usize, u64> = HashMap::new();
        for term in formula.split('+') {
            match try_parse_int(term) {
                Some(n) => value += n,
                None => *counts.entry(self.cell(term)).or_default() += 1,
            }
        }
        for (used, _) in mem::take(&mut self.uses[edited]) {
            self.users[used].remove(&edited);
        }
        for (&used, &count) in &counts {
            value += &self.values[used] * count;
            self.users[used].insert(edited, count);
        }
        self.uses[edited] = counts.into_iter().collect();
        value
    }

    /// The cells that depend on `edited`, it included, each before those that read it; or `None`
    /// if the walk comes back to `edited`. The sheet before this edit had no cycle, so any cycle
    /// holds `edited` and this finds it.
    fn dependents(&mut self, edited: usize, edit: usize) -> Option<Vec<usize>> {
        let Sheet { users, seen, .. } = self;
        let mut order = Vec::new();
        let mut stack: Vec<(usize, Keys<'_, usize, u64>)> = vec![(edited, users[edited].keys())];
        seen[edited] = edit;
        while let Some((cell, readers)) = stack.last_mut() {
            match readers.next() {
                Some(&user) if user == edited => return None,
                Some(&user) if seen[user] != edit => {
                    seen[user] = edit;
                    stack.push((user, users[user].keys()));
                }
                Some(_) => {}
                None => {
                    order.push(*cell);
                    stack.pop();
                }
            }
        }
        order.reverse();
        Some(order)
    }

    /// Hands the change in value of each cell of `order` on to the cells that read it.
    fn spread(&mut self, order: &[usize]) {
        for &cell in order {
            let change = mem::take(&mut self.changes[cell]);
            if change.is_zero() {
                continue;
            }
            for (&user, &count) in &self.users[cell] {
                self.changes[user] += &change * count;
            }
            self.values[cell] += change;
            self.shown[cell] = format!("{}={}", self.names[cell], self.values[cell]);
        }
    }
}

/// The term at which a walk of `formulas` from each cell in name order first finds a cell that
/// depends on itself. The error names the term of this walk.
fn first_cycle<'a>(formulas: &BTreeMap<&'a str, &'a str>) -> Option<&'a str> {
    let mut open: HashMap<&str, bool> = HashMap::new();
    for (&name, &formula) in formulas {
        if open.contains_key(name) {
            continue;
        }
        open.insert(name, true);
        let mut stack: Vec<(&str, Split<'_, char>)> = vec![(name, formula.split('+'))];
        while let Some((cell, terms)) = stack.last_mut() {
            let Some(term) = terms.next() else {
                open.insert(cell, false);
                stack.pop();
                continue;
            };
            if try_parse_int(term).is_some() {
                continue;
            }
            match open.get(term) {
                Some(true) => return Some(term),
                Some(false) => {}
                None => {
                    if let Some((&name, &formula)) = formulas.get_key_value(term) {
                        open.insert(name, true);
                        stack.push((name, formula.split('+')));
                    }
                }
            }
        }
    }
    None
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut sheet = Sheet::default();
    let mut formulas: BTreeMap<&str, &str> = BTreeMap::new();
    let mut defined: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, l) in lines.iter().enumerate() {
        let mut parts = l.split(" = ");
        let name = parts.next().unwrap_or("");
        let formula = parts.next().unwrap_or("0");
        formulas.insert(name, formula);
        let edited = sheet.cell(name);
        defined.insert(name, edited);
        let value = sheet.set_formula(edited, formula);
        let Some(order) = sheet.dependents(edited, i + 1) else {
            let term = first_cycle(&formulas).expect("the walk came back to the edited cell");
            return Err(format!("the cell {term} depends on itself"));
        };
        sheet.changes[edited] = value - &sheet.values[edited];
        sheet.spread(&order);
        if sheet.shown[edited].is_empty() {
            sheet.shown[edited] = format!("{name}={}", sheet.values[edited]);
        }
        let shown: Vec<&str> = defined.values().map(|&c| sheet.shown[c].as_str()).collect();
        say!(out, "{}", shown.join(" "));
    }
    Ok(())
}

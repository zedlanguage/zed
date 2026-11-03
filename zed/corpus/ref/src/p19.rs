//! 19 bank ledger. A withdrawal above the balance turns the balance into the failure (tx index,
//! shortfall); a failed balance stays that failure through later transactions (atom
//! pass-through). Accounts print in name order; the total and count are over the accounts whose
//! balance is an int.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::Zero;

use crate::zedrt::parse_int;

enum Balance {
    Funds(BigInt),
    Insufficient { tx: usize, short: BigInt },
}

use Balance::{Funds, Insufficient};

fn account<'m>(accts: &'m mut BTreeMap<&str, Balance>, i: &str) -> Result<&'m mut Balance, String> {
    accts.get_mut(i).ok_or_else(|| format!("no account {i}"))
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let mut accts: BTreeMap<&str, Balance> = BTreeMap::new();
    for (t, l) in lines.iter().enumerate() {
        let mut w = l.split(' ');
        let (kind, i) = (w.next().unwrap_or(""), w.next().unwrap_or(""));
        let amt = w.next().map_or(Ok(BigInt::zero()), parse_int)?;
        match kind {
            "dep" => {
                if let Funds(amount) = account(&mut accts, i)? {
                    *amount += amt;
                }
            }
            "wd" => {
                let balance = account(&mut accts, i)?;
                if let Funds(amount) = balance {
                    if amt > *amount {
                        let short = amt - &*amount;
                        *balance = Insufficient { tx: t, short };
                    } else {
                        *amount -= amt;
                    }
                }
            }
            "open" => {
                accts.insert(i, Funds(BigInt::zero()));
            }
            _ => {}
        }
    }
    let (mut total, mut good) = (BigInt::zero(), 0);
    for (i, balance) in &accts {
        match balance {
            Insufficient { tx, short } => say!(out, "{i}: insufficient at tx {tx}, short {short}"),
            Funds(amount) => {
                say!(out, "{i}: {amount}");
                total += amount;
                good += 1;
            }
        }
    }
    let failed = accts.len() - good;
    say!(out, "total {total} over {good} accounts, {failed} failed");
    Ok(())
}

/// 19 bank ledger. A withdrawal above the balance turns the balance into the failure (tx
/// index, shortfall); a failed balance stays that failure through later transactions (atom
/// pass-through). Accounts print in name order; the total and count are over the accounts
/// whose balance is an int.
library;

import 'zedrt.dart';

sealed class Balance {}

final class Funds extends Balance {
  Funds(this.amount);
  final BigInt amount;
}

final class Insufficient extends Balance {
  Insufficient(this.tx, this.short);
  final int tx;
  final BigInt short;
}

void main(List<String> args) {
  final accts = <String, Balance>{};
  for (final (t, l) in readLines(args[0]).indexed) {
    final w = l.split(' ');
    final (kind, i) = (w[0], w.length > 1 ? w[1] : '');
    final amt = w.length > 2 ? parseInt(w[2]) : BigInt.zero;
    switch (kind) {
      case 'open':
        accts[i] = Funds(BigInt.zero);
      case 'dep':
        if (accts[i]! case Funds(:final amount)) accts[i] = Funds(amount + amt);
      case 'wd':
        if (accts[i]! case Funds(:final amount)) {
          accts[i] = amt > amount ? Insufficient(t, amt - amount) : Funds(amount - amt);
        }
    }
  }
  for (final i in sortedByCodePoint(accts.keys)) {
    print(switch (accts[i]!) {
      Insufficient(:final tx, :final short) => '$i: insufficient at tx $tx, short $short',
      Funds(:final amount) => '$i: $amount',
    });
  }
  final good = [
    for (final v in accts.values)
      if (v case Funds(:final amount)) amount,
  ];
  final total = good.fold(BigInt.zero, (a, b) => a + b);
  print('total $total over ${good.length} accounts, ${accts.length - good.length} failed');
}

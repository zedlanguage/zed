/// 15 spreadsheet: after each edit, every cell's value in name order (code-point order). A
/// term is an integer when int() reads it (zedrt.tryParseInt), else a cell name; an empty
/// cell is 0. #set inserts or replaces.
library;

import 'zedrt.dart';

BigInt value(Map<String, String> sheet, String name) {
  final formula = sheet[name];
  if (formula == null) return BigInt.zero;
  var total = BigInt.zero;
  for (final t in formula.split('+')) {
    total += tryParseInt(t) ?? value(sheet, t);
  }
  return total;
}

void main(List<String> args) {
  final sheet = <String, String>{};
  for (final l in readLines(args[0])) {
    final parts = l.split(' = ');
    sheet[parts[0]] = parts.length > 1 ? parts[1] : '0';
    print(sortedByCodePoint(sheet.keys).map((c) => '$c=${value(sheet, c)}').join(' '));
  }
}
